#!/usr/bin/env python3
"""Check local release build planning and fail-closed artifact validation."""

import importlib.util
import os
from pathlib import Path
import tempfile
import struct
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

    def test_windows_plan_uses_explicit_sdk_and_executable_suffix(self):
        with patch.dict(os.environ, {"XWIN_ROOT": "/sdk with spaces"}, clear=True):
            command, env, output = build.build_plan('x86_64-pc-windows-msvc', LINUX)
        self.assertEqual(command[-1], 'x86_64-pc-windows-msvc')
        self.assertEqual(output.name, 'venticornserver.exe')
        self.assertEqual(env['CARGO_TARGET_X86_64_PC_WINDOWS_MSVC_LINKER'], 'lld-link')
        self.assertIn('-Lnative=/sdk with spaces/crt/lib/x86_64', env['CARGO_ENCODED_RUSTFLAGS'].split('\x1f'))

    def test_windows_crossbuild_rejects_unconfigured_sdk(self):
        with patch.dict(os.environ, {}, clear=True), patch.object(build, 'require_tool'):
            with self.assertRaisesRegex(ValueError, 'XWIN_ROOT'):
                build.preflight('x86_64-pc-windows-msvc', LINUX)

    def test_windows_artifact_must_be_x64_pe(self):
        with tempfile.TemporaryDirectory() as folder:
            executable = Path(folder) / 'venticornserver.exe'
            data = bytearray(70)
            data[:2] = b'MZ'
            struct.pack_into('<I', data, 60, 64)
            data[64:] = b'PE\0\0\x64\x86'
            executable.write_bytes(data)
            build.validate_artifact('x86_64-pc-windows-msvc', executable)
            data[68:70] = b'\x64\xaa'
            executable.write_bytes(data)
            with self.assertRaisesRegex(ValueError, 'x64 PE'):
                build.validate_artifact('x86_64-pc-windows-msvc', executable)

    def test_macos_build_preserves_flags_without_static_crt(self):
        with patch.dict(os.environ, {"CARGO_ENCODED_RUSTFLAGS": "-C\x1fdebuginfo=1"}, clear=True):
            native, env, _ = build.build_plan('aarch64-apple-darwin', 'aarch64-apple-darwin')
            cross, _, _ = build.build_plan('aarch64-apple-darwin', LINUX)
        self.assertEqual(native[1], 'build')
        self.assertEqual(cross[1], 'zigbuild')
        self.assertEqual(env['CARGO_ENCODED_RUSTFLAGS'], '-C\x1fdebuginfo=1')

    def test_macos_crossbuild_rejects_unconfigured_sdk(self):
        with patch.dict(os.environ, {}, clear=True), patch.object(build, 'require_tool'):
            with self.assertRaisesRegex(ValueError, 'SDKROOT'):
                build.preflight('aarch64-apple-darwin', LINUX)

    def test_macos_artifact_architecture_and_dependencies(self):
        with tempfile.TemporaryDirectory() as folder:
            executable = Path(folder) / 'venticornserver'
            for name, valid in [(b'/usr/lib/libSystem.B.dylib', True),
                                (b'@rpath/libonnxruntime.dylib', False)]:
                command = struct.pack('<IIIIII', 0xC, 25 + len(name), 24, 0, 0, 0) + name + b'\0'
                header = struct.pack('<IIIIIIII', 0xFEEDFACF, 0x0100000C, 0, 2, 1, len(command), 0, 0)
                executable.write_bytes(header + command)
                if valid:
                    build.validate_artifact('aarch64-apple-darwin', executable)
                else:
                    with self.assertRaisesRegex(ValueError, 'non-system library'):
                        build.validate_artifact('aarch64-apple-darwin', executable)
            executable.write_bytes(b'not a Mach-O executable')
            with self.assertRaisesRegex(ValueError, 'ARM Mach-O'):
                build.validate_artifact('aarch64-apple-darwin', executable)

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
