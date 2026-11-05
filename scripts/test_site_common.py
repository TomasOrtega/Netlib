"""Check provenance coverage for documentation inputs."""

import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import site_common


class InputTests(unittest.TestCase):
    def test_python_caches_do_not_change_source_tree(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            source = root / "examples/capture/exercise.py"
            source.parent.mkdir(parents=True)
            source.write_text("print('capture')\n")
            evidence = source.parent / "native/frame.bin"
            evidence.parent.mkdir()
            evidence.write_bytes(bytes([0, 1, 2]))
            with patch.object(site_common, "ROOT", root):
                before = site_common.input_hashes()
                for relative in [
                    "__pycache__/exercise.cpython-312.pyc",
                    "__pycache__/exercise.cpython-315.pyc",
                    "__pycache__/cache-metadata",
                    "exercise.pyc",
                    "exercise.pyo",
                ]:
                    cache = source.parent / relative
                    cache.parent.mkdir(parents=True, exist_ok=True)
                    cache.write_bytes(b"local interpreter output")
                self.assertEqual(before, site_common.input_hashes())
                self.assertIn("examples/capture/exercise.py", before)
                self.assertIn("examples/capture/native/frame.bin", before)
                source.write_text("print('changed capture')\n")
                after = site_common.input_hashes()
                self.assertNotEqual(before, after)
                evidence.write_bytes(bytes([0, 1, 3]))
                self.assertNotEqual(after, site_common.input_hashes())

    def test_nested_research_note_changes_source_tree(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            note = root / "docs/research/QUEUE.md"
            note.parent.mkdir(parents=True)
            note.write_text("Initial source evidence.\n")
            with patch.object(site_common, "ROOT", root):
                before = site_common.input_hashes()
                self.assertIn("docs/research/QUEUE.md", before)
                note.write_text("Revised source evidence.\n")
                after = site_common.input_hashes()
                self.assertNotEqual(site_common.tree_hash(before), site_common.tree_hash(after))
                note.unlink()
                self.assertNotIn("docs/research/QUEUE.md", site_common.input_hashes())


if __name__ == "__main__":
    unittest.main()
