"""Check that CI cannot select a local compiler hook."""

import tempfile
import unittest
from pathlib import Path

import yaml
from check_source import check_ci


class CiTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / ".github/workflows").mkdir(parents=True)

    def write(self, *, stages=None, entry="lake build", command="uv run --locked prek -a --quiet"):
        hook = {"id": "build", "entry": entry, "language": "system"}
        if stages is not None:
            hook["stages"] = stages
        config = {"default_stages": ["pre-commit"], "repos": [{"repo": "local", "hooks": [hook]}]}
        (self.root / ".pre-commit-config.yaml").write_text(yaml.safe_dump(config))
        workflow = {"jobs": {"check": {"steps": [{"run": command}]}}}
        (self.root / ".github/workflows/check.yml").write_text(yaml.safe_dump(workflow))

    def test_local_compiler_stays_manual(self):
        self.write(stages=["manual"])
        self.assertEqual(check_ci(self.root), [])

    def test_default_hook_cannot_compile(self):
        self.write()
        self.assertTrue(check_ci(self.root))

    def test_direct_build_fails(self):
        self.write(stages=["manual"], command="lake build")
        self.assertTrue(check_ci(self.root))

    def test_manual_stage_in_ci_fails(self):
        self.write(stages=["manual"], command="uv run prek -a --stage manual")
        self.assertTrue(check_ci(self.root))

    def test_static_python_hook_passes(self):
        self.write(entry="uv run --locked python scripts/check_text.py")
        self.assertEqual(check_ci(self.root), [])


if __name__ == "__main__":
    unittest.main()
