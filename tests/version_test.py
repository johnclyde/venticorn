#!/usr/bin/env python3
"""Exercise release version changes against disposable repository fixtures."""

import importlib.util
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("version", ROOT / "python/version.py")
version = importlib.util.module_from_spec(spec)
spec.loader.exec_module(version)


class VersionTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        for original in version.release_files(ROOT):
            destination = self.root / original.relative_to(ROOT)
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(original, destination)

    def contents(self):
        return {p.relative_to(self.root): p.read_bytes() for p in version.release_files(self.root)}

    def test_check_is_read_only(self):
        before = self.contents()
        self.assertRegex(version.update_version(self.root), r'^\d+\.\d+\.\d+$')
        self.assertEqual(before, self.contents())

    def test_updates_root_versions_preserving_dependencies(self):
        before = version.tomllib.loads((self.root / "Cargo.lock").read_text())
        npm_before = json.loads((self.root / "vscode/extension/package-lock.json").read_text())
        self.assertEqual(version.update_version(self.root, "12.34.56"), "12.34.56")
        self.assertEqual(version.update_version(self.root), "12.34.56")
        after = version.tomllib.loads((self.root / "Cargo.lock").read_text())
        self.assertEqual([p for p in before['package'] if p['name'] != 'venticorn'],
                         [p for p in after['package'] if p['name'] != 'venticorn'])
        npm_after = json.loads((self.root / "vscode/extension/package-lock.json").read_text())
        self.assertEqual({k: v for k, v in npm_before['packages'].items() if k},
                         {k: v for k, v in npm_after['packages'].items() if k})

    def test_invalid_versions_leave_every_file_unchanged(self):
        before = self.contents()
        for invalid in ["1.2", "1.2.3.4", "01.2.3", "1.2.-3", "1.2.3\n", "1.2.3-beta"]:
            with self.subTest(invalid=invalid), self.assertRaises(ValueError):
                version.update_version(self.root, invalid)
            self.assertEqual(before, self.contents())

    def test_staging_failure_leaves_every_original_unchanged(self):
        before = self.contents()
        original_stage = version.stage_text
        count = 0

        def fail_staging(path, text):
            nonlocal count
            count += 1
            if count == 3:
                raise OSError("simulated full disk while staging")
            return original_stage(path, text)

        with patch.object(version, "stage_text", side_effect=fail_staging):
            with self.assertRaisesRegex(OSError, "full disk"):
                version.update_version(self.root, "12.34.56")
        self.assertEqual(before, self.contents())
        self.assertFalse(list(self.root.rglob(".*.*")))

    def test_replacement_failure_rolls_back_completed_replacements(self):
        before = self.contents()
        original_replace = version.os.replace
        count = 0

        def fail_second_replace(source, destination):
            nonlocal count
            count += 1
            if count == 2:
                raise OSError("simulated replace failure")
            return original_replace(source, destination)

        with patch.object(version.os, "replace", side_effect=fail_second_replace):
            with self.assertRaisesRegex(OSError, "replace failure"):
                version.update_version(self.root, "12.34.56")
        self.assertEqual(before, self.contents())
        self.assertFalse(list(self.root.rglob(".*.*")))

    def test_version_file_mismatch_is_rejected(self):
        (self.root / "VERSION").write_text("98.76.54\n")
        before = self.contents()
        with self.assertRaisesRegex(ValueError, "disagree"):
            version.update_version(self.root, "12.34.56")
        self.assertEqual(before, self.contents())

    def test_mismatch_is_rejected_before_any_write(self):
        path = self.root / "vscode/extension/package.json"
        data = json.loads(path.read_text())
        data['version'] = "98.76.54"
        path.write_text(json.dumps(data))
        before = self.contents()
        with self.assertRaisesRegex(ValueError, 'disagree'):
            version.update_version(self.root, "12.34.56")
        self.assertEqual(before, self.contents())


if __name__ == "__main__":
    unittest.main()
