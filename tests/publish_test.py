#!/usr/bin/env python3
"""Release upload checks with fake binaries and mocked GitHub commands."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "python"))
spec = importlib.util.spec_from_file_location("publish", Path(__file__).resolve().parents[1] / "python/publish.py")
publish = importlib.util.module_from_spec(spec)
spec.loader.exec_module(publish)


class ReleaseAssetsTest(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        (self.root / "VERSION").write_text("0.1.0\n")
        package = self.root / "vscode/extension/package.json"
        package.parent.mkdir(parents=True)
        manifest = {"name": "venticorn-extension", "version": "0.1.0"}
        package.write_text(json.dumps(manifest))
        package.with_name("package-lock.json").write_text(json.dumps({**manifest, "packages": {"": manifest}}))
        (self.root / "Cargo.toml").write_text('[package]\nname = "venticorn"\nversion = "0.1.0"\n')
        (self.root / "Cargo.lock").write_text('[[package]]\nname = "venticorn"\nversion = "0.1.0"\n')
        for platform, target, suffix in publish.PLATFORMS:
            binary = self.root / "target" / target / "release" / ("venticornserver" + suffix)
            binary.parent.mkdir(parents=True)
            binary.write_bytes(platform.encode())

    def test_dry_run_has_no_writes_or_network(self):
        with patch.object(publish.subprocess, "run") as run:
            publish.publish(self.root, "dry-run")
        run.assert_not_called()
        self.assertFalse((self.root / "files").exists())

    def test_staged_names_match_download_platforms(self):
        with patch.object(publish.subprocess, "run") as run:
            publish.publish(self.root, "stage")
        run.assert_not_called()
        staging = self.root / "files/release/v0.1.0"
        self.assertEqual(sorted(p.name for p in staging.iterdir()), [
            "venticornserver-v0.1.0-darwin-arm64",
            "venticornserver-v0.1.0-linux-x64",
            "venticornserver-v0.1.0-win32-x64.exe",
        ])
        for platform, _, suffix in publish.PLATFORMS:
            self.assertEqual((staging / f"venticornserver-v0.1.0-{platform}{suffix}").read_text(), platform)

    def test_all_artifacts_are_checked_before_network_or_staging(self):
        last = self.root / "target/aarch64-apple-darwin/release/venticornserver"
        last.unlink()
        with patch.object(publish.subprocess, "run") as run, self.assertRaisesRegex(ValueError, "Missing or empty"):
            publish.publish(self.root, "upload")
        run.assert_not_called()
        self.assertFalse((self.root / "files").exists())

    def test_upload_uses_explicit_repository_without_clobber(self):
        with patch.object(publish.subprocess, "run") as run:
            publish.publish(self.root, "upload")
        self.assertEqual(run.call_args_list[0].args[0], ["gh", "release", "view", "v0.1.0", "--repo", "johnclyde/venticorn"])
        upload = run.call_args_list[1].args[0]
        self.assertEqual(upload[:6], ["gh", "release", "upload", "v0.1.0", "--repo", "johnclyde/venticorn"])
        self.assertEqual(len(upload[6:]), 3)
        self.assertNotIn("--clobber", upload)

    def test_missing_release_stops_before_staging(self):
        with patch.object(publish.subprocess, "run", side_effect=subprocess.CalledProcessError(1, "gh")), self.assertRaises(subprocess.CalledProcessError):
            publish.publish(self.root, "upload")
        self.assertFalse((self.root / "files").exists())

    def test_cargo_and_npm_lock_mismatches_stop_direct_entry_before_network(self):
        for relative in ["Cargo.toml", "Cargo.lock", "vscode/extension/package-lock.json"]:
            with self.subTest(path=relative):
                file = self.root / relative
                original = file.read_text()
                file.write_text(original.replace("0.1.0", "0.2.0"))
                with patch.object(publish.subprocess, "run") as run, self.assertRaisesRegex(ValueError, "disagree"):
                    publish.publish(self.root, "upload")
                run.assert_not_called()
                self.assertFalse((self.root / "files").exists())
                file.write_text(original)

    def test_invalid_or_mismatched_version_is_rejected(self):
        for value in ["../bad", "0.1.1", "00.1.0"]:
            (self.root / "VERSION").write_text(value)
            with self.assertRaises(ValueError):
                publish.release_plan(self.root)


if __name__ == "__main__":
    unittest.main()
