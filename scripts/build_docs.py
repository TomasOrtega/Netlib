"""Build and save the manual and API site on this machine."""

import gzip
import json
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
from html import escape
from pathlib import Path

from check_site import check_links
from package_api import package_api
from site_common import ARCHIVE, MANIFEST, ROOT, digest, input_hashes, tree_hash

GROUPS = {
    "Theory": "Prove FIFO conservation, backlog bounds, and finite draining.",
    "Core": "State requirements as logic formulas.",
    "Model": "Read a finite network model.",
    "Network": "Compose domains and prove path, failure, and update properties.",
    "Packet": "Partition headers and check ordered rules for complete traffic classes.",
    "Routing": "Select the route with the longest address prefix.",
    "Security": "Check requests at policy gateways.",
    "Policy": "Parse requirements and find missing goals.",
    "Check": "Check claims with proof-backed results.",
    "Compile": "Compile packet intent to certified ACLs and structured nftables policies.",
    "Examples": "Read complete architecture proofs.",
    "Standards": "Compose formal profiles and check selected Wi-Fi and 5G requirements.",
    "Import": "Read strict hostapd, Linux route, and nftables snapshots.",
    "Protocol": "Compose transition traces and prove session and admission properties.",
}


def run(*args, cwd=ROOT):
    subprocess.run(args, cwd=cwd, check=True)


def revision():
    result = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True, capture_output=True, check=True
    )
    return result.stdout.strip()


def require_saved_source():
    source = ["Netlib.lean", "Main.lean", "Netlib"]
    result = subprocess.run(
        ["git", "diff", "--name-only", "HEAD", "--", *source],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=True,
    )
    new = subprocess.run(
        ["git", "ls-files", "--others", "--exclude-standard", "--", *source],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=True,
    )
    if result.stdout.strip() or new.stdout.strip():
        raise SystemExit(
            "Commit the Lean source before the docs build. Source links need that commit."
        )


def landing(directory, version, source_revision, stats):
    modules = sorted((ROOT / "Netlib").rglob("*.lean"))
    cards = []
    for group, text in GROUPS.items():
        members = [p for p in modules if p.relative_to(ROOT / "Netlib").parts[0] == group]
        if not members:
            continue
        preferred = next((p for p in members if p.stem == "Basic"), members[0])
        url = "api/" + preferred.relative_to(ROOT).with_suffix(".html").as_posix()
        count = f"{len(members)} module" + ("" if len(members) == 1 else "s")
        cards.append(
            f'<section class="card"><h3><a href="{escape(url)}">{escape(group)}</a>'
            f'</h3><p>{escape(text)}</p><span class="label">{count}</span></section>'
        )
    values = {
        "lean_version": version,
        "revision": source_revision,
        "short_revision": source_revision[:8],
        "module_count": str(stats["modules"]),
        "declaration_count": str(stats["declarations"]),
        "module_cards": "\n".join(cards),
    }
    template = (ROOT / "docs/assets/index.html").read_text()
    for key, value in values.items():
        template = template.replace("{{" + key + "}}", value)
    (directory / "index.html").write_text(template)
    shutil.copy2(ROOT / "docs/assets/site.css", directory / "site.css")
    (directory / ".nojekyll").write_text("")


def licenses(directory):
    target = directory / "licenses"
    target.mkdir()
    links = []
    for package in ["doc-gen4", "verso"]:
        source = ROOT / ".lake/packages" / package / "LICENSE"
        if not source.exists():
            raise FileNotFoundError(f"Find the tool license: {source}")
        name = package + ".txt"
        shutil.copy2(source, target / name)
        links.append(f'<li><a href="{name}">{package}</a></li>')
    (target / "index.html").write_text(
        '<!doctype html><html lang="en"><meta charset="utf-8"><title>Tool licenses</title>'
        "<h1>Tool licenses</h1><ul>" + "".join(links) + '</ul><a href="../">Netlib</a></html>'
    )


def manual_anchors(directory):
    # Verso chapter links include a tag that its first heading can omit.
    for page in directory.glob("*/index.html"):
        if page.parent.name in ["find", "search"]:
            continue
        text = page.read_text()
        tag = escape(page.parent.name, quote=True)
        if f'id="{tag}"' not in text:
            page.write_text(text.replace("<h1>", f'<h1 id="{tag}">', 1))


def pack(directory):
    ARCHIVE.parent.mkdir(exist_ok=True)
    with ARCHIVE.open("wb") as output:
        with gzip.GzipFile(fileobj=output, mode="wb", filename="", mtime=0) as compressed:
            with tarfile.open(fileobj=compressed, mode="w") as archive:
                for path in sorted(directory.rglob("*")):
                    if not path.is_file():
                        continue
                    entry = archive.gettarinfo(str(path), path.relative_to(directory).as_posix())
                    entry.uid = entry.gid = 0
                    entry.uname = entry.gname = ""
                    entry.mtime = 0
                    entry.mode = 0o644
                    with path.open("rb") as content:
                        archive.addfile(entry, content)


def main():
    require_saved_source()
    inputs = input_hashes()
    source_revision = revision()
    run("lake", "--wfail", "build")
    run("lake", "test")
    run(sys.executable, "scripts/check_cli.py")
    run(sys.executable, "scripts/check_profiles.py")
    run(sys.executable, "scripts/check_source.py")
    run(sys.executable, "scripts/check_text.py")
    project = ROOT / "docbuild"
    run("lake", "--wfail", "build", "manual", cwd=project)
    run("lake", "exe", "manual", "--output", "../.lake/manual", cwd=project)
    run("lake", "build", "netlib/Netlib:docs", cwd=project)
    if input_hashes() != inputs:
        raise SystemExit("Source files changed during the build. Build the docs again.")
    with tempfile.TemporaryDirectory(prefix="netlib-docs-") as folder:
        site = Path(folder)
        stats = package_api(project / ".lake/build/doc", site / "api")
        # Keep source links on the exact source commit.
        for page in site.joinpath("api").rglob("*.html"):
            text = page.read_text()
            text = re.sub(
                r"(https://github\.com/TomasOrtega/Netlib/(?:blob|tree)/)[^/]+/",
                lambda m: m[1] + source_revision + "/",
                text,
            )
            page.write_text(text)
        shutil.copytree(ROOT / ".lake/manual/html-multi", site / "manual")
        manual_anchors(site / "manual")
        version = (ROOT / "lean-toolchain").read_text().strip().split(":v")[-1]
        landing(site, version, source_revision, stats)
        licenses(site)
        pages = sum(1 for _ in site.rglob("*.html"))
        config = json.loads((project / "lake-manifest.json").read_text())
        tools = {
            p["name"].strip("«»"): p["rev"]
            for p in config["packages"]
            if p["name"].strip("«»") in ["doc-gen4", "verso"]
        }
        if set(tools) != {"doc-gen4", "verso"}:
            raise ValueError("Record both documentation tool versions.")
        provenance = {
            "schema": 1,
            "lean_version": version,
            "source_revision": source_revision,
            "source_tree": tree_hash(inputs),
            "inputs": inputs,
            "tools": tools,
            "api": stats,
            "html_pages": pages,
        }
        (site / "provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")
        check_links(site.resolve())
        pack(site)
    manifest = {**provenance, "archive_sha256": digest(ARCHIVE.read_bytes())}
    MANIFEST.write_text(json.dumps(manifest, indent=2) + "\n")
    run(sys.executable, "scripts/check_site.py")
    print(f"Saved {pages} HTML pages in {ARCHIVE.relative_to(ROOT)}.")


if __name__ == "__main__":
    main()
