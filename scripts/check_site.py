"""Check the saved site package. Do not run a compiler."""

import argparse
import html
from html.parser import HTMLParser
import json
from pathlib import Path, PurePosixPath
import re
import shutil
import sys
import tarfile
import tempfile
from urllib.parse import unquote, urljoin, urlsplit

from site_common import ARCHIVE, MANIFEST, digest, input_hashes, tree_hash


class Page(HTMLParser):
    def __init__(self, text):
        super().__init__(convert_charrefs=True)
        self.base = ""
        self.links = []
        self.ids = set()
        self.feed(text)

    def handle_starttag(self, tag, attrs):
        fields = dict(attrs)
        if fields.get("id"):
            self.ids.add(fields["id"])
        if tag == "a" and fields.get("name"):
            self.ids.add(fields["name"])
        if tag == "base":
            self.base = fields.get("href", "")
            return
        for field in ["href", "src"]:
            if fields.get(field):
                self.links.append(fields[field])


def check_links(directory):
    directory = directory.resolve()
    origin = "https://netlib.invalid/Netlib/"
    parsed = {p: Page(p.read_text()) for p in directory.rglob("*.html")}
    errors = []

    def check(path, link, base):
        absolute = urljoin(base, html.unescape(link))
        parts = urlsplit(absolute)
        if parts.scheme not in ("http", "https") or parts.netloc != "netlib.invalid":
            return
        if not parts.path.startswith("/Netlib/"):
            errors.append(f"{path.relative_to(directory)}: Link leaves the site path: {link}")
            return
        relative = unquote(parts.path.removeprefix("/Netlib/"))
        target = (directory / relative).resolve()
        if not target.is_relative_to(directory.resolve()):
            errors.append(f"{path.relative_to(directory)}: Link leaves the site folder: {link}")
            return
        if target.is_dir():
            target /= "index.html"
        if not target.is_file():
            errors.append(f"{path.relative_to(directory)}: Link has no file: {link}")
        elif parts.fragment and target in parsed:
            fragment = unquote(parts.fragment)
            if (fragment != "top" and fragment not in parsed[target].ids
                    and not fragment.startswith(":~:text=")):
                errors.append(f"{path.relative_to(directory)}: Link has no anchor: {link}")

    for path, page in parsed.items():
        base = urljoin(origin, path.relative_to(directory).as_posix())
        base = urljoin(base, page.base)
        for link in page.links:
            check(path, link, base)
    for path in directory.rglob("*.css"):
        base = urljoin(origin, path.relative_to(directory).as_posix())
        for link in re.findall(r"url\(\s*['\"]?([^)'\"\s]+)", path.read_text()):
            check(path, link, base)
    data = directory / "api/declarations/declaration-data.bmp"
    if data.exists():
        index = json.loads(data.read_text())
        for declaration in index["declarations"].values():
            check(data, declaration["docLink"], origin + "api/")
        for module in index["modules"].values():
            check(data, module["url"], origin + "api/")
    if errors:
        raise ValueError("\n".join(errors[:50]) +
                         (f"\n{len(errors)} links failed." if len(errors) > 50 else ""))
    return len(parsed)


def extract(archive, destination):
    with tarfile.open(archive, "r:gz") as saved:
        seen = set()
        for member in saved.getmembers():
            name = PurePosixPath(member.name)
            canonical = name.as_posix()
            if (name.is_absolute() or ".." in name.parts or "\\" in member.name
                    or not name.parts or not member.isfile() or canonical in seen):
                raise ValueError(f"Reject the archive entry: {member.name}")
            seen.add(canonical)
            target = destination.joinpath(*name.parts)
            target.parent.mkdir(parents=True, exist_ok=True)
            with saved.extractfile(member) as source, target.open("wb") as output:
                shutil.copyfileobj(source, output)


def validate(destination):
    manifest = json.loads(MANIFEST.read_text())
    if manifest.get("schema") != 1:
        raise ValueError("Use site manifest schema 1.")
    current = input_hashes()
    if manifest.get("inputs") != current:
        changed = sorted(set(current) | set(manifest.get("inputs", {})))
        changed = [p for p in changed if current.get(p) != manifest.get("inputs", {}).get(p)]
        raise ValueError("Build the site again. These inputs changed:\n" + "\n".join(changed))
    if manifest.get("source_tree") != tree_hash(current):
        raise ValueError("The source tree hash does not match.")
    if manifest.get("archive_sha256") != digest(ARCHIVE.read_bytes()):
        raise ValueError("The archive hash does not match.")
    extract(ARCHIVE, destination)
    provenance = json.loads((destination / "provenance.json").read_text())
    if provenance != {k: v for k, v in manifest.items() if k != "archive_sha256"}:
        raise ValueError("The site and manifest have different source records.")
    pages = check_links(destination.resolve())
    print(f"Site checks passed for {pages} HTML pages. The source hashes match.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--extract", type=Path, help="Write the checked site to this folder.")
    args = parser.parse_args()
    try:
        if args.extract:
            destination = args.extract.resolve()
            if destination.exists() and any(destination.iterdir()):
                raise ValueError("Use an empty output folder.")
            destination.mkdir(parents=True, exist_ok=True)
            validate(destination)
        else:
            with tempfile.TemporaryDirectory(prefix="netlib-site-") as folder:
                validate(Path(folder))
    except (ValueError, OSError, KeyError, tarfile.TarError) as error:
        print(error, file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
