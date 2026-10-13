#!/usr/bin/env python3
"""Check local release build planning and fail-closed artifact validation."""

import importlib.util
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("crossbuild", ROOT / "python/crossbuild.py")
build = importlib.util.module_from_spec(spec)
spec.loader.exec_module(build)
LINUX = "x86_64-unknown-linux-gnu"


class CrossbuildTest(unittest.TestCase):
    def test_linux_plan_is_locked_and_static_with_scoped_flags(self):
        with patch.dict(os.environ, {"RUSTFLAGS": "-C debuginfo=1"}, clear=True):
            command, env, output = build.build_plan(LINUX, LINUX)
            self.assertNotIn('CARGO_ENCODED_RUSTFLAGS', os.environ)
        self.assertEqual(command, ['cargo', 'build', '--locked', '--release', '--bin',
                                   'venticornserver', '--target', LINUX])
        self.assertEqual(env['CARGO_ENCODED_RUSTFLAGS'], '-C\x1fdebuginfo=1\x1f-C\x1ftarget-feature=+crt-static')
        self.assertEqual(output, ROOT / 'target' / LINUX / 'release/venticornserver')
        self.assertEqual(env['CARGO_TARGET_DIR'], str(ROOT / 'target'))

    def test_heuristic_build_is_explicit(self):
        command, _, _ = build.build_plan(LINUX, LINUX, True)
        self.assertIn('--no-default-features', command)

    def test_unknown_target_fails(self):
        with self.assertRaisesRegex(ValueError, 'unsupported target'):
            build.build_plan('invented-target', LINUX)

    def test_foreign_linux_build_requires_native_toolchain(self):
        with patch.object(build, 'require_tool'):
            with self.assertRaisesRegex(ValueError, 'native build host'):
                build.preflight(LINUX, 'aarch64-apple-darwin')

    def test_missing_artifact_is_rejected(self):
        with tempfile.TemporaryDirectory() as folder:
            with self.assertRaisesRegex(ValueError, 'expected artifact'):
                build.validate_artifact(LINUX, Path(folder) / 'absent')

    def test_dynamic_linux_binary_is_rejected(self):
        with tempfile.NamedTemporaryFile() as artifact:
            for headers, dynamic in [('INTERP', ''), ('', ' (NEEDED) libfoo.so')]:
                outputs = [type('Result', (), {'stdout': headers})(), type('Result', (), {'stdout': dynamic})()]
                with patch.object(build, 'run', side_effect=outputs):
                    with self.assertRaisesRegex(ValueError, 'statically linked'):
                        build.validate_artifact(LINUX, Path(artifact.name))
            with patch.object(build, 'run', return_value=type('Result', (), {'stdout': ''})()):
                build.validate_artifact(LINUX, Path(artifact.name))


if __name__ == '__main__':
    unittest.main()
