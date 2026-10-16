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
        with patch.dict(os.environ, {}, clear=True), patch.object(build, 'require_tool'), patch.object(build, 'windows_inspector'):
            with self.assertRaisesRegex(ValueError, 'XWIN_ROOT'):
                build.preflight('x86_64-pc-windows-msvc', LINUX, True)

    def test_windows_artifact_must_be_x64_pe(self):
        with tempfile.TemporaryDirectory() as folder:
            executable = Path(folder) / 'venticornserver.exe'
            data = bytearray(70)
            data[:2] = b'MZ'
            struct.pack_into('<I', data, 60, 64)
            data[64:] = b'PE\0\0\x64\x86'
            executable.write_bytes(data)
            with patch.object(build, 'validate_windows_imports') as imports:
                build.validate_artifact('x86_64-pc-windows-msvc', executable)
                imports.assert_called_once_with(executable)
            data[68:70] = b'\x64\xaa'
            executable.write_bytes(data)
            with self.assertRaisesRegex(ValueError, 'x64 PE'):
                build.validate_artifact('x86_64-pc-windows-msvc', executable)

    def test_windows_onnx_requires_an_explicit_static_runtime(self):
        target = "x86_64-pc-windows-msvc"
        with patch.dict(os.environ, {}, clear=True), patch.object(build, "require_tool"), patch.object(build, "windows_inspector"):
            with self.assertRaisesRegex(ValueError, "ORT_LIB_LOCATION"):
                build.preflight(target, target)
        with tempfile.TemporaryDirectory() as folder, patch.dict(os.environ, {"ORT_LIB_LOCATION": folder, "ORT_PREFER_DYNAMIC_LINK": "true"}, clear=True), patch.object(build, "require_tool"), patch.object(build, "windows_inspector"):
            with self.assertRaisesRegex(ValueError, "static ONNX Runtime"):
                build.preflight(target, target)

    def test_windows_onnx_plan_preserves_explicit_location_and_static_choice(self):
        target = "x86_64-pc-windows-msvc"
        with tempfile.TemporaryDirectory() as folder, patch.dict(os.environ, {"ORT_LIB_LOCATION": folder}, clear=True):
            _, env, _ = build.build_plan(target, target)
        self.assertEqual(env["ORT_LIB_LOCATION"], str(Path(folder).resolve()))
        self.assertEqual(env["ORT_PREFER_DYNAMIC_LINK"], "0")
        self.assertIn("target-feature=+crt-static", env["CARGO_ENCODED_RUSTFLAGS"])

    def test_windows_import_check_accepts_system_dlls_and_rejects_runtime_dlls(self):
        for output in ["  KERNEL32.dll\n  ADVAPI32.dll\n", "Import {\n  Name: KERNEL32.dll\n}\n"]:
            with patch.object(build, "windows_inspector", return_value=["inspector"]), patch.object(build, "run", return_value=type("Result", (), {"stdout": output})()):
                build.validate_windows_imports(Path("server.exe"))
        for dll in ["onnxruntime.dll", "VCRUNTIME140.dll", "MSVCP140.dll", "ucrtbase.dll", "api-ms-win-crt-runtime-l1-1-0.dll"]:
            # Delay-load imports are checked too, rather than ignored after ordinary imports.
            output = f"Import {{\n  Name: KERNEL32.dll\n}}\nDelayImport {{\n  Name: {dll}\n}}\n"
            with self.subTest(dll=dll), patch.object(build, "windows_inspector", return_value=["inspector"]), patch.object(build, "run", return_value=type("Result", (), {"stdout": output})()):
                with self.assertRaisesRegex(ValueError, "dynamic runtime libraries"):
                    build.validate_windows_imports(Path("server.exe"))

    def test_windows_import_check_fails_if_inspection_is_unavailable_or_empty(self):
        with patch.object(build.shutil, "which", return_value=None):
            with self.assertRaisesRegex(ValueError, "dumpbin or llvm-readobj"):
                build.windows_inspector()
        with patch.object(build, "windows_inspector", return_value=["inspector"]), patch.object(build, "run", return_value=type("Result", (), {"stdout": "unexpected output"})()):
            with self.assertRaisesRegex(ValueError, "no DLL names"):
                build.validate_windows_imports(Path("server.exe"))

    def test_macos_build_preserves_flags_without_static_crt(self):
        with patch.dict(os.environ, {"CARGO_ENCODED_RUSTFLAGS": "-C\x1fdebuginfo=1"}, clear=True):
            native, env, _ = build.build_plan('aarch64-apple-darwin', 'aarch64-apple-darwin')
            cross, _, _ = build.build_plan('aarch64-apple-darwin', LINUX)
        self.assertEqual(native[1], 'build')
        self.assertEqual(cross[1], 'zigbuild')
        self.assertEqual(env['CARGO_ENCODED_RUSTFLAGS'], '-C\x1fdebuginfo=1')

    def test_macos_crossbuild_normalizes_sdkroot_only_in_child_environment(self):
        with tempfile.TemporaryDirectory() as home:
            for supplied in ["~/macsdk", "relative sdk", "/sdk with spaces"]:
                with self.subTest(sdkroot=supplied), patch.dict(
                        os.environ, {"HOME": home, "SDKROOT": supplied}, clear=True):
                    expected = str(Path(supplied).expanduser().resolve())
                    command, env, _ = build.build_plan('aarch64-apple-darwin', LINUX)
                    self.assertEqual(command[1], 'zigbuild')
                    self.assertEqual(env['SDKROOT'], expected)
                    self.assertEqual(os.environ['SDKROOT'], supplied)
                    _, native_env, _ = build.build_plan(
                        'aarch64-apple-darwin', 'aarch64-apple-darwin')
                    self.assertEqual(native_env['SDKROOT'], supplied)

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
