"""Share the site paths and source hashes."""

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ARCHIVE = ROOT / "docs/site.tar.gz"
MANIFEST = ROOT / "docs/site-manifest.json"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def input_hashes():
    paths = {
        ROOT / name
        for name in [
            "README.md",
            "GLOSSARY.md",
            "Netlib.lean",
            "Main.lean",
            "lean-toolchain",
            "lakefile.toml",
            "lake-manifest.json",
            "pyproject.toml",
            "uv.lock",
            ".python-version",
            "docbuild/lakefile.toml",
            "docbuild/lean-toolchain",
            "docbuild/lake-manifest.json",
            "scripts/build_docs.py",
            "scripts/package_api.py",
            "scripts/site_common.py",
            "scripts/check_site.py",
            "scripts/check_profiles.py",
        ]
    }
    paths.update((ROOT / "Netlib").rglob("*.lean"))
    paths.update((ROOT / "docbuild").glob("*.lean"))
    paths.update((ROOT / "docs").glob("*.md"))
    paths.update((ROOT / "docs/assets").rglob("*"))
    paths.update((ROOT / "examples").rglob("*"))
    return {
        p.relative_to(ROOT).as_posix(): digest(p.read_bytes()) for p in sorted(paths) if p.is_file()
    }


def tree_hash(inputs):
    return digest(json.dumps(inputs, sort_keys=True, separators=(",", ":")).encode())
