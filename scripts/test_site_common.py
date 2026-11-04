"""Check provenance coverage for documentation inputs."""

import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import site_common


class InputTests(unittest.TestCase):
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
