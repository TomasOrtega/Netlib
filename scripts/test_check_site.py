"""Test site links, archive entries, and source records."""

from contextlib import redirect_stdout
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest
from unittest.mock import patch

import check_site


class SiteTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="netlib-site-test-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        self.site = self.root / "site"
        self.site.mkdir()

    def write(self, name, text):
        target = self.site / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)
        return target

    def test_root_base_path(self):
        self.write("index.html", '<base href="/Netlib/"><a href="api/module.html#proof">API</a>')
        self.write("api/module.html", '<base href="/Netlib/api/"><h1 id="proof">Proof</h1>'
                   '<a href="../index.html">Start</a>')
        self.assertEqual(check_site.check_links(self.site), 2)

    def test_deep_relative_links(self):
        self.write("api/Netlib/Packet/Basic.html",
                   '<a href="../Network/Basic.html#gateway">Gateway</a>')
        self.write("api/Netlib/Network/Basic.html", '<h1 id="gateway">Gateway</h1>')
        self.assertEqual(check_site.check_links(self.site), 2)

    def test_deep_relative_base(self):
        self.write("api/Netlib/Packet/Basic.html",
                   '<base href="../../"><a href="Netlib/Network/Basic.html#gateway">Gateway</a>')
        self.write("api/Netlib/Network/Basic.html", '<h1 id="gateway">Gateway</h1>')
        self.assertEqual(check_site.check_links(self.site), 2)

    def test_missing_file(self):
        self.write("index.html", '<a href="missing.html">Missing</a>')
        with self.assertRaisesRegex(ValueError, "Link has no file"):
            check_site.check_links(self.site)

    def test_missing_anchor(self):
        self.write("index.html", '<a href="page.html#missing">Missing</a>')
        self.write("page.html", '<h1 id="present">Page</h1>')
        with self.assertRaisesRegex(ValueError, "Link has no anchor"):
            check_site.check_links(self.site)

    def test_top_and_text_fragments(self):
        self.write("index.html", '<a href="#top">Top</a>'
                   '<a href="#:~:text=Use%20the%20model">Text</a>')
        self.assertEqual(check_site.check_links(self.site), 1)

    def test_named_and_encoded_anchors(self):
        self.write("index.html", '<a href="page.html#field%20name">Field</a>'
                   '<a href="page.html#legacy">Old link</a>')
        self.write("page.html", '<h1 id="field name">Field</h1><a name="legacy"></a>')
        self.assertEqual(check_site.check_links(self.site), 2)

    def test_directory_index_and_external_links(self):
        self.write("index.html", '<a href="manual/">Manual</a>'
                   '<a href="https://example.com/missing">Source</a>'
                   '<a href="mailto:person@example.com">Mail</a>')
        self.write("manual/index.html", '<h1>Manual</h1>')
        self.assertEqual(check_site.check_links(self.site), 2)

    def declaration_data(self, link="Netlib/Packet/Basic.html#Header"):
        self.write("api/Netlib/Packet/Basic.html", '<h1 id="Header">Header</h1>')
        self.write("api/declarations/declaration-data.bmp", json.dumps({
            "declarations": {"Netlib.Packet.Header": {"docLink": link}},
            "modules": {"Netlib.Packet.Basic": {"url": "Netlib/Packet/Basic.html"}},
        }))

    def test_declaration_data_links(self):
        self.declaration_data()
        self.assertEqual(check_site.check_links(self.site), 1)

    def test_declaration_data_missing_anchor(self):
        self.declaration_data("Netlib/Packet/Basic.html#missing")
        with self.assertRaisesRegex(ValueError, "Link has no anchor"):
            check_site.check_links(self.site)

    def test_css_asset_links(self):
        self.write("index.html", '<link rel="stylesheet" href="css/main.css">')
        self.write("css/main.css", "@font-face {src: url('../fonts/lean.woff2')}\n"
                   '.icon {background: url("../images/icon.svg")}\n'
                   ".remote {background: url(https://example.com/icon.svg)}\n"
                   ".inline {background: url(data:image/svg+xml,abc)}")
        self.write("fonts/lean.woff2", "font")
        self.write("images/icon.svg", "<svg></svg>")
        self.assertEqual(check_site.check_links(self.site), 1)

    def test_missing_css_asset(self):
        self.write("css/main.css", "body {background: url(missing.png)}")
        with self.assertRaisesRegex(ValueError, "Link has no file"):
            check_site.check_links(self.site)

    def test_link_leaves_site_path(self):
        self.write("index.html", '<a href="../outside.html">Outside</a>')
        with self.assertRaisesRegex(ValueError, "Link leaves the site path"):
            check_site.check_links(self.site)

    def test_encoded_link_leaves_site_folder(self):
        self.write("index.html", '<a href="%2e%2e/outside.html">Outside</a>')
        (self.root / "outside.html").write_text("Outside")
        with self.assertRaisesRegex(ValueError, "Link leaves the site folder"):
            check_site.check_links(self.site)

    def test_link_through_symlink_leaves_site_folder(self):
        outside = self.root / "outside.html"
        outside.write_text("Outside")
        (self.site / "linked.html").symlink_to(outside)
        self.write("index.html", '<a href="linked.html">Outside</a>')
        with self.assertRaisesRegex(ValueError, "Link leaves the site folder"):
            check_site.check_links(self.site)


class ArchiveTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="netlib-archive-test-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.archive = self.root / "site.tar.gz"
        self.destination = self.root / "output"
        self.destination.mkdir()

    def save(self, entries):
        with tarfile.open(self.archive, "w:gz") as archive:
            for name, content, kind in entries:
                entry = tarfile.TarInfo(name)
                entry.type = kind
                entry.linkname = "../outside"
                entry.size = len(content) if kind == tarfile.REGTYPE else 0
                archive.addfile(entry, io.BytesIO(content) if entry.isfile() else None)

    def test_normal_roundtrip(self):
        self.save([("index.html", b"Start", tarfile.REGTYPE),
                   ("api/module.html", b"Module", tarfile.REGTYPE)])
        check_site.extract(self.archive, self.destination)
        self.assertEqual((self.destination / "index.html").read_bytes(), b"Start")
        self.assertEqual((self.destination / "api/module.html").read_bytes(), b"Module")

    def test_reject_parent_paths(self):
        for name in ["../outside", "api/../../outside", r"api\outside"]:
            with self.subTest(name=name):
                self.save([(name, b"Bad", tarfile.REGTYPE)])
                with self.assertRaisesRegex(ValueError, "Reject the archive entry"):
                    check_site.extract(self.archive, self.destination)
        self.assertFalse((self.root / "outside").exists())

    def test_reject_absolute_path(self):
        self.save([("/outside", b"Bad", tarfile.REGTYPE)])
        with self.assertRaisesRegex(ValueError, "Reject the archive entry"):
            check_site.extract(self.archive, self.destination)

    def test_reject_link_and_special_entries(self):
        for kind in [tarfile.SYMTYPE, tarfile.LNKTYPE, tarfile.DIRTYPE, tarfile.FIFOTYPE]:
            with self.subTest(kind=kind):
                self.save([("entry", b"", kind)])
                with self.assertRaisesRegex(ValueError, "Reject the archive entry"):
                    check_site.extract(self.archive, self.destination)

    def test_reject_duplicate_path(self):
        self.save([("index.html", b"First", tarfile.REGTYPE),
                   ("index.html", b"Second", tarfile.REGTYPE)])
        with self.assertRaisesRegex(ValueError, "Reject the archive entry"):
            check_site.extract(self.archive, self.destination)

    def test_reject_duplicate_path_alias(self):
        for original, alias in [("index.html", "./index.html"),
                                ("index.html", "././index.html"),
                                ("api/module.html", "api//module.html")]:
            with self.subTest(alias=alias):
                self.save([(original, b"First", tarfile.REGTYPE),
                           (alias, b"Second", tarfile.REGTYPE)])
                with self.assertRaisesRegex(ValueError, "Reject the archive entry"):
                    check_site.extract(self.archive, self.destination)


class ManifestTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="netlib-record-test-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.archive = self.root / "site.tar.gz"
        self.manifest = self.root / "site-manifest.json"
        self.destination = self.root / "output"
        self.destination.mkdir()
        self.inputs = {"Netlib/Core/Logic.lean": check_site.digest(b"source")}
        self.record = {
            "schema": 1,
            "lean_version": "4.35.0",
            "source_revision": "a" * 40,
            "source_tree": check_site.tree_hash(self.inputs),
            "inputs": self.inputs,
        }
        self.write_package()
        self.addCleanup(patch.stopall)
        patch.object(check_site, "ARCHIVE", self.archive).start()
        patch.object(check_site, "MANIFEST", self.manifest).start()
        patch.object(check_site, "input_hashes", return_value=self.inputs).start()

    def write_package(self, provenance=None):
        entries = {
            "index.html": b'<h1 id="start">Start</h1><a href="#top">Top</a>',
            "provenance.json": json.dumps(self.record if provenance is None else provenance).encode(),
        }
        with tarfile.open(self.archive, "w:gz") as archive:
            for name, content in entries.items():
                entry = tarfile.TarInfo(name)
                entry.size = len(content)
                archive.addfile(entry, io.BytesIO(content))
        saved = {**self.record, "archive_sha256": check_site.digest(self.archive.read_bytes())}
        self.manifest.write_text(json.dumps(saved))

    def validate(self):
        with redirect_stdout(io.StringIO()) as output:
            check_site.validate(self.destination)
        return output.getvalue()

    def test_normal_package_roundtrip(self):
        self.assertIn("Site checks passed for 1 HTML pages", self.validate())
        self.assertTrue((self.destination / "index.html").is_file())
        self.assertEqual(json.loads((self.destination / "provenance.json").read_text()), self.record)

    def test_stale_source_hash(self):
        with patch.object(check_site, "input_hashes", return_value={"Netlib/Core/Logic.lean": "changed"}):
            with self.assertRaisesRegex(ValueError, "These inputs changed.*\\nNetlib/Core/Logic.lean"):
                self.validate()

    def test_stale_source_tree_hash(self):
        self.record["source_tree"] = "changed"
        self.write_package()
        with self.assertRaisesRegex(ValueError, "source tree hash does not match"):
            self.validate()

    def test_stale_archive_hash(self):
        self.archive.write_bytes(self.archive.read_bytes() + b"changed")
        with self.assertRaisesRegex(ValueError, "archive hash does not match"):
            self.validate()

    def test_provenance_mismatch(self):
        self.write_package({**self.record, "source_revision": "b" * 40})
        with self.assertRaisesRegex(ValueError, "different source records"):
            self.validate()

    def test_unknown_schema(self):
        self.record["schema"] = 2
        self.write_package()
        with self.assertRaisesRegex(ValueError, "Use site manifest schema 1"):
            self.validate()


if __name__ == "__main__":
    unittest.main()
