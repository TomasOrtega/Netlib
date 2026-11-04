"""Export the Netlib API pages from a local doc-gen4 build."""

import argparse
from collections import deque
import html
from html.parser import HTMLParser
import json
from pathlib import Path, PurePosixPath
import posixpath
import re
import shutil
from urllib.parse import unquote, urlsplit


UPSTREAM_API = "https://lean-lang.org/doc/api/"
URL_ATTRIBUTE = re.compile(
    r"(?P<prefix>\b(?:href|src)\s*=\s*)(?P<quote>[\"'])(?P<url>.*?)(?P=quote)",
    re.IGNORECASE | re.DOTALL,
)
JS_IMPORT = re.compile(
    r"(?:\bfrom\s*|\bimport\s*)[\"'](?P<url>\.[^\"']+)[\"']"
)
CSS_URL = re.compile(r"url\(\s*[\"']?(?P<url>[^\s\)\"']+)")


def _local_path(page: PurePosixPath, value: str) -> PurePosixPath | None:
    url = urlsplit(html.unescape(value))
    if url.scheme or url.netloc or not url.path or url.path.startswith("/"):
        return None
    path = PurePosixPath(posixpath.normpath(str(page.parent / unquote(url.path))))
    if path == PurePosixPath("..") or str(path).startswith("../"):
        return None
    return path


class _Attributes(HTMLParser):
    def __init__(self, text: str, transform=None):
        super().__init__(convert_charrefs=False)
        self.text = text
        self.transform = transform
        self.links = []
        self.changes = []
        self.lines = [0]
        for match in re.finditer("\n", text):
            self.lines.append(match.end())

    def handle_starttag(self, tag, attrs):
        raw = self.get_starttag_text()
        self.links.extend(
            value for key, value in attrs if key in {"href", "src"} and value
        )
        if self.transform is None:
            return

        def replace(match):
            value = html.unescape(match["url"])
            target = self.transform(value)
            if target == value:
                return match[0]
            quote = match["quote"]
            return f'{match["prefix"]}{quote}{html.escape(target, quote=True)}{quote}'

        replacement = URL_ATTRIBUTE.sub(replace, raw)
        if replacement != raw:
            line, column = self.getpos()
            start = self.lines[line - 1] + column
            self.changes.append((start, start + len(raw), replacement))

    handle_startendtag = handle_starttag

    def result(self):
        result = self.text
        for start, end, replacement in reversed(self.changes):
            result = result[:start] + replacement + result[end:]
        return result


def _attributes(text: str, transform=None) -> _Attributes:
    parser = _Attributes(text, transform)
    parser.feed(text)
    parser.close()
    return parser


def _module_page(path: PurePosixPath) -> bool:
    return path.suffix == ".html" and (
        path == PurePosixPath("Netlib.html") or path.parts[0] == "Netlib"
    )


def _replace_main(text: str, content: str) -> str:
    result, count = re.subn(r"<main(?:\s[^>]*)?>.*?</main>", content, text, flags=re.DOTALL)
    if count != 1:
        raise ValueError("The API page must contain one main element.")
    return result


def _navigation(modules: dict) -> str:
    links = "\n".join(
        '<div class="nav_link"><a href="{}">{}</a></div>'.format(
            html.escape(info["url"], quote=True), html.escape(name)
        )
        for name, info in sorted(modules.items())
    )
    return f'''<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Netlib API navigation</title>
<link rel="stylesheet" href="style.css">
<script type="module" src="nav.js"></script>
<script type="module" src="color-scheme.js"></script>
<base target="_parent"></head><body><div class="navframe"><nav class="nav">
<h3>Netlib API</h3>
<div class="nav_link"><a href="index.html">API index</a></div>
<div class="nav_link"><a href="search.html">Search</a></div>
<div class="nav_link"><a href="../manual/">Manual</a></div>
<h3>Modules</h3>{links}
<div id="settings" hidden><h3>Color scheme</h3>
<form id="color-theme-switcher">
<label><input type="radio" name="color_theme" value="system">system</label>
<label><input type="radio" name="color_theme" value="light">light</label>
<label><input type="radio" name="color_theme" value="dark">dark</label>
</form></div></nav></div></body></html>
'''


def package_api(source: Path, destination: Path) -> dict:
    source = source.resolve()
    destination = destination.resolve()
    if source == destination or source in destination.parents:
        raise ValueError("The API export must use a separate directory.")
    if destination.exists() and any(destination.iterdir()):
        raise ValueError("The API export directory must be empty.")

    index_path = source / "declarations/declaration-data.bmp"
    full_index = json.loads(index_path.read_text())
    build_manifest = source.parent / "doc-manifest.json"
    current_pages = None
    if build_manifest.is_file():
        current_pages = set()
        for value in json.loads(build_manifest.read_text()):
            page = PurePosixPath(value)
            if page.parts[0] == source.name:
                page = PurePosixPath(*page.parts[1:])
            current_pages.add(page)
    modules = {
        name: {
            "url": info["url"],
            "importedBy": info["importedBy"],
        }
        for name, info in full_index["modules"].items()
        if (name == "Netlib" or name.startswith("Netlib."))
        and (
            current_pages is None
            or _local_path(PurePosixPath("index.html"), info["url"]) in current_pages
        )
    }
    for info in modules.values():
        info["importedBy"] = [name for name in info["importedBy"] if name in modules]
    module_pages = {
        _local_path(PurePosixPath("index.html"), info["url"])
        for info in modules.values()
    }
    if not modules or None in module_pages:
        raise ValueError("The doc-gen4 output has no valid Netlib module index.")
    if any(not _module_page(page) for page in module_pages):
        raise ValueError("The Netlib module index contains an invalid page path.")

    declarations = {
        name: info
        for name, info in full_index["declarations"].items()
        if _local_path(PurePosixPath("index.html"), info["docLink"]) in module_pages
    }
    if not declarations:
        raise ValueError("The doc-gen4 output has no Netlib declarations.")

    def instances(field):
        return {
            name: filtered
            for name, values in full_index[field].items()
            if (filtered := [value for value in values if value in declarations])
        }

    index = {
        "declarations": declarations,
        "modules": modules,
        "instances": instances("instances"),
        "instancesFor": instances("instancesFor"),
    }
    pages = {
        page: (source / str(page)).read_text()
        for page in module_pages | {
            PurePosixPath("index.html"),
            PurePosixPath("search.html"),
            PurePosixPath("404.html"),
            PurePosixPath("find/index.html"),
        }
    }
    pages[PurePosixPath("index.html")] = _replace_main(
        pages[PurePosixPath("index.html")],
        '<main><a id="top"></a><h1>Netlib API</h1>'
        '<p>These pages describe the Netlib declarations and proofs.</p>'
        '<p><a href="Netlib.html">Open the library root.</a> '
        '<a href="../manual/">Read the manual.</a></p></main>',
    )
    pages[PurePosixPath("404.html")] = _replace_main(
        pages[PurePosixPath("404.html")],
        '<main><h1>Page not found</h1>'
        '<p>Use the module list or search to find a declaration.</p>'
        '<div id="howabout"></div></main>',
    )
    pages[PurePosixPath("navbar.html")] = _navigation(modules)

    dependency_pages = set()
    for page, text in pages.items():
        for value in _attributes(text).links:
            target = _local_path(page, value)
            if target and target.suffix == ".html" and target not in pages:
                dependency_pages.add(target)

    source_links = {}
    for page in dependency_pages:
        module = ".".join(page.with_suffix("").parts)
        data = source / "declarations" / f"declaration-data-{module}.bmp"
        if not data.is_file():
            continue
        for declaration in json.loads(data.read_text()).get("declarations", []):
            info = declaration["info"]
            link = info.get("sourceLink", "")
            if link.startswith(("https://", "http://")):
                source_links[page, unquote(urlsplit(info["docLink"]).fragment)] = link

    def externalize(page, value):
        target = _local_path(page, value)
        if target not in dependency_pages:
            return value
        url = urlsplit(value)
        fragment = unquote(url.fragment)
        exact_source = source_links.get((target, fragment))
        if exact_source:
            return exact_source
        suffix = f"?{url.query}" if url.query else ""
        suffix += f"#{url.fragment}" if url.fragment else ""
        return UPSTREAM_API + target.as_posix() + suffix

    destination.mkdir(parents=True, exist_ok=True)
    required = deque()
    for page, text in pages.items():
        rendered = _attributes(text, lambda value: externalize(page, value)).result()
        target = destination / str(page)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(rendered)
        required.extend(
            path
            for value in _attributes(rendered).links
            if (path := _local_path(page, value)) is not None
        )

    data_target = destination / "declarations/declaration-data.bmp"
    data_target.parent.mkdir(parents=True, exist_ok=True)
    data_target.write_text(json.dumps(index, ensure_ascii=False, separators=(",", ":")))
    copied = set(pages) | {PurePosixPath("declarations/declaration-data.bmp")}
    while required:
        path = required.popleft()
        if path in copied or path == PurePosixPath("."):
            continue
        original = source / str(path)
        if original.is_dir():
            path = path / "index.html"
            original = source / str(path)
        if path in copied:
            continue
        if path.suffix == ".html":
            raise ValueError(f"The API export contains an unexpected page link: {path}")
        if not original.is_file():
            raise ValueError(f"The API export needs a missing asset: {path}")
        target = destination / str(path)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(original, target)
        copied.add(path)
        if path.suffix in {".js", ".css"}:
            text = original.read_text()
            patterns = (JS_IMPORT,) if path.suffix == ".js" else (CSS_URL,)
            for pattern in patterns:
                for match in pattern.finditer(text):
                    dependency = _local_path(path, match["url"])
                    if dependency is not None:
                        required.append(dependency)

    return {
        "pages": len(pages),
        "modules": len(modules),
        "declarations": len(declarations),
        "files": len(copied),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("destination", type=Path)
    args = parser.parse_args()
    print(json.dumps(package_api(args.source, args.destination), sort_keys=True))


if __name__ == "__main__":
    main()
