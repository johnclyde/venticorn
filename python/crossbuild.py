#!/usr/bin/env python3
"""Build local release-server artifacts without installing tools or publishing."""

import argparse
import os
import re
from pathlib import Path
import shutil
import subprocess
import struct
import sys

ROOT = Path(__file__).resolve().parents[1]
TARGETS = {
    "x86_64-unknown-linux-gnu": ("linux-x64", "venticornserver"),
    "x86_64-pc-windows-msvc": ("win32-x64", "venticornserver.exe"),
    "aarch64-apple-darwin": ("darwin-arm64", "venticornserver"),
}


def run(command, *, env=None):
    return subprocess.run(command, cwd=ROOT, env=env, check=True, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def require_tool(name):
    if not shutil.which(name):
        raise ValueError(f"required build tool is missing: {name}")


def host_target():
    require_tool("rustc")
    for line in run(["rustc", "-vV"]).stdout.splitlines():
        if line.startswith("host: "):
            return line.removeprefix("host: ")
    raise ValueError("rustc did not report its host target")


def build_plan(target, host, no_default_features=False):
    if target not in TARGETS:
        raise ValueError(f"unsupported target: {target}; choose one of {', '.join(TARGETS)}")
    command = ["cargo", "build", "--locked", "--release", "--bin", "venticornserver", "--target", target]
    if no_default_features:
        command.append("--no-default-features")
    env = os.environ.copy()
    # Set flags only for this explicit target build; host build scripts retain host flags.
    rustflags = env.get("CARGO_ENCODED_RUSTFLAGS")
    if rustflags is None:
        # Cargo's plain RUSTFLAGS format is whitespace-separated.
        rustflags = '\x1f'.join(env.get("RUSTFLAGS", "").split())
    if target != "aarch64-apple-darwin":
        rustflags += ('\x1f' if rustflags else '') + "-C\x1ftarget-feature=+crt-static"
    env["CARGO_ENCODED_RUSTFLAGS"] = rustflags
    env.pop("RUSTFLAGS", None)
    if target == "x86_64-pc-windows-msvc" and not no_default_features:
        # The Windows release must use a matching static ONNX Runtime build.
        env["ORT_PREFER_DYNAMIC_LINK"] = "0"
        if env.get("ORT_LIB_LOCATION"):
            env["ORT_LIB_LOCATION"] = str(Path(env["ORT_LIB_LOCATION"]).expanduser().resolve())
    if target == "x86_64-pc-windows-msvc" and target != host:
        env["CARGO_TARGET_X86_64_PC_WINDOWS_MSVC_LINKER"] = env.get(
            "CARGO_TARGET_X86_64_PC_WINDOWS_MSVC_LINKER", "lld-link")
        if env.get("XWIN_ROOT"):
            root = Path(env["XWIN_ROOT"]).expanduser().resolve()
            for directory in ("crt/lib/x86_64", "sdk/lib/um/x86_64", "sdk/lib/ucrt/x86_64"):
                env["CARGO_ENCODED_RUSTFLAGS"] += "\x1f-Lnative=" + str(root / directory)
    if target == "aarch64-apple-darwin" and not host.endswith("-apple-darwin"):
        command[1] = "zigbuild"
    # A fixed output path is part of the release-staging contract.
    env["CARGO_TARGET_DIR"] = str(ROOT / "target")
    output = ROOT / "target" / target / "release" / TARGETS[target][1]
    return command, env, output


def preflight(target, host, no_default_features=False):
    require_tool("cargo")
    require_tool("rustc")
    if target == "x86_64-unknown-linux-gnu":
        if target != host:
            raise ValueError(f"{target} requires a native build host; current Rust host is {host}")
        require_tool("readelf")
    elif target == "x86_64-pc-windows-msvc":
        windows_inspector()
        if not no_default_features:
            location = os.environ.get("ORT_LIB_LOCATION")
            if not location or not Path(location).expanduser().is_dir():
                raise ValueError("Windows ONNX builds require ORT_LIB_LOCATION pointing to an ONNX Runtime 1.19.2 static build; use --no-default-features for the heuristic scorer")
            if os.environ.get("ORT_PREFER_DYNAMIC_LINK", "0").lower() in ("1", "true"):
                raise ValueError("Windows releases require a static ONNX Runtime; remove ORT_PREFER_DYNAMIC_LINK")
        if target == host:
            require_tool(os.environ.get("CARGO_TARGET_X86_64_PC_WINDOWS_MSVC_LINKER", "link.exe"))
            if not os.environ.get("LIB"):
                raise ValueError("Windows builds require an MSVC developer shell with SDK LIB paths")
        else:
            root_text = os.environ.get("XWIN_ROOT")
            if not root_text:
                raise ValueError("Windows cross-builds require an explicit XWIN_ROOT SDK directory")
            root = Path(root_text).expanduser().resolve()
            for directory in ("crt/lib/x86_64", "sdk/lib/um/x86_64", "sdk/lib/ucrt/x86_64"):
                if not (root / directory).is_dir():
                    raise ValueError(f"Windows SDK library directory is missing: {root / directory}")
            require_tool(os.environ.get("CARGO_TARGET_X86_64_PC_WINDOWS_MSVC_LINKER", "lld-link"))
    elif target == "aarch64-apple-darwin":
        if host.endswith("-apple-darwin"):
            require_tool("xcrun")
            sdk = Path(run(["xcrun", "--show-sdk-path"]).stdout.strip())
        else:
            require_tool("cargo-zigbuild")
            require_tool("zig")
            sdk_text = os.environ.get("SDKROOT")
            if not sdk_text:
                raise ValueError("macOS cross-builds require an explicit SDKROOT")
            sdk = Path(sdk_text).expanduser().resolve()
        if not (sdk / "usr/lib").is_dir() or not (sdk / "System/Library/Frameworks").is_dir():
            raise ValueError(f"macOS SDK libraries/frameworks are missing: {sdk}")
    target_lib = Path(run(["rustc", "--print", "target-libdir", "--target", target]).stdout.strip())
    if not target_lib.is_dir():
        raise ValueError(f"Rust standard library is missing for {target}; install that target explicitly")


def validate_artifact(target, path):
    if not path.is_file():
        raise ValueError(f"build succeeded without the expected artifact: {path}")
    if target == "x86_64-pc-windows-msvc":
        # Validate the actual PE signature and machine rather than asking ldd about Windows.
        with path.open("rb") as executable:
            header = executable.read(64)
            if len(header) != 64 or header[:2] != b"MZ":
                raise ValueError("Windows release server is not a PE executable")
            executable.seek(struct.unpack_from("<I", header, 60)[0])
            signature = executable.read(6)
            if signature != b"PE\0\0\x64\x86":
                raise ValueError("Windows release server must be an x64 PE executable")
        validate_windows_imports(path)
        return
    if target == "aarch64-apple-darwin":
        validate_macho(path)
        return
    # Inspect our own ELF output; do not execute a foreign program with ldd.
    headers = run(["readelf", "-l", str(path)]).stdout
    dynamic = run(["readelf", "-d", str(path)]).stdout
    if "INTERP" in headers or "(NEEDED)" in dynamic:
        raise ValueError("Linux release server must be statically linked (ELF interpreter/dependencies found)")


def windows_inspector():
    if shutil.which("dumpbin"):
        return ["dumpbin", "/DEPENDENTS"]
    if shutil.which("llvm-readobj"):
        # Includes ordinary and delay-load imports.
        return ["llvm-readobj", "--coff-imports"]
    raise ValueError("Windows artifact checks require dumpbin or llvm-readobj")


def validate_windows_imports(path):
    output = run([*windows_inspector(), str(path)]).stdout
    # Parse dependency-name lines only, not imported symbol names or file paths.
    imports = {match.lower() for match in re.findall(
        r"^\s*(?:Name:\s*)?([A-Za-z0-9_.-]+\.dll)\s*$", output, re.MULTILINE | re.IGNORECASE)}
    if not imports:
        raise ValueError("Windows dependency inspector reported no DLL names; cannot validate runtime linkage")
    forbidden = sorted(name for name in imports if name.startswith(
        ("onnxruntime", "vcruntime", "msvcp", "msvcr", "concrt", "ucrtbase", "ucrtbased", "api-ms-win-crt-")))
    if forbidden:
        raise ValueError("Windows release server requires dynamic runtime libraries: " + ", ".join(forbidden))
    print("Windows imported libraries: " + ", ".join(sorted(imports)))


def validate_macho(path):
    """Inspect a thin ARM64 Mach-O and reject non-system dynamic dependencies."""
    with path.open("rb") as executable:
        header = executable.read(32)
        if len(header) != 32 or struct.unpack_from("<II", header) != (0xFEEDFACF, 0x0100000C):
            raise ValueError("macOS release server must be a 64-bit ARM Mach-O executable")
        count, size = struct.unpack_from("<II", header, 16)
        if size > path.stat().st_size - 32:
            raise ValueError("invalid Mach-O load-command size")
        commands = executable.read(size)
    offset = 0
    dylib_commands = {0xC, 0x80000018, 0x8000001F, 0x20, 0x80000023}
    for _ in range(count):
        if offset + 8 > len(commands):
            raise ValueError("truncated Mach-O load command")
        command, length = struct.unpack_from("<II", commands, offset)
        if length < 8 or offset + length > len(commands):
            raise ValueError("invalid Mach-O load command")
        if command in dylib_commands:
            if length < 24:
                raise ValueError("truncated Mach-O library command")
            name_offset = struct.unpack_from("<I", commands, offset + 8)[0]
            if name_offset < 24 or name_offset >= length:
                raise ValueError("invalid Mach-O library path")
            name_bytes = commands[offset + name_offset:offset + length]
            if b"\0" not in name_bytes:
                raise ValueError("unterminated Mach-O library path")
            name = name_bytes.split(b"\0", 1)[0].decode("utf-8")
            if not name.startswith(("/usr/lib/", "/System/Library/")):
                raise ValueError(f"macOS release server requires a non-system library: {name}")
        offset += length
    if offset != len(commands):
        raise ValueError("Mach-O load commands do not match their declared size")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("targets", nargs="*", metavar="TARGET", help="explicit Rust target triples")
    parser.add_argument("--plan", action="store_true", help="show commands without building or checking SDKs")
    parser.add_argument("--no-default-features", action="store_true", help="build with the heuristic scorer")
    args = parser.parse_args()
    try:
        host = host_target()
        targets = list(dict.fromkeys(args.targets or [host]))
        plans = [(target, build_plan(target, host, args.no_default_features)) for target in targets]
        if not args.plan:
            for target, _ in plans:
                preflight(target, host, args.no_default_features)
        for target, (command, env, output) in plans:
            print(f"{TARGETS[target][0]}: {' '.join(command)}", flush=True)
            print(f"output: {output}", flush=True)
            print(f"target flags: {env.get('CARGO_ENCODED_RUSTFLAGS', '').replace(chr(31), ' ')}", flush=True)
            if args.plan:
                continue
            subprocess.run(command, cwd=ROOT, env=env, check=True)
            validate_artifact(target, output)
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        parser.exit(1, f"crossbuild: {error}\n")


if __name__ == "__main__":
    main()
