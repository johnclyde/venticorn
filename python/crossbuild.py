#!/usr/bin/env python3
"""Build local release-server artifacts without installing tools or publishing."""

import argparse
import os
from pathlib import Path
import shutil
import subprocess
import struct
import sys

ROOT = Path(__file__).resolve().parents[1]
TARGETS = {
    "x86_64-unknown-linux-gnu": ("linux-x64", "venticornserver"),
    "x86_64-pc-windows-msvc": ("win32-x64", "venticornserver.exe"),
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
    env["CARGO_ENCODED_RUSTFLAGS"] = rustflags + ('\x1f' if rustflags else '') + "-C\x1ftarget-feature=+crt-static"
    env.pop("RUSTFLAGS", None)
    if target == "x86_64-pc-windows-msvc" and target != host:
        env["CARGO_TARGET_X86_64_PC_WINDOWS_MSVC_LINKER"] = env.get(
            "CARGO_TARGET_X86_64_PC_WINDOWS_MSVC_LINKER", "lld-link")
        if env.get("XWIN_ROOT"):
            root = Path(env["XWIN_ROOT"]).expanduser().resolve()
            for directory in ("crt/lib/x86_64", "sdk/lib/um/x86_64", "sdk/lib/ucrt/x86_64"):
                env["CARGO_ENCODED_RUSTFLAGS"] += "\x1f-Lnative=" + str(root / directory)
    # A fixed output path is part of the release-staging contract.
    env["CARGO_TARGET_DIR"] = str(ROOT / "target")
    output = ROOT / "target" / target / "release" / TARGETS[target][1]
    return command, env, output


def preflight(target, host):
    require_tool("cargo")
    require_tool("rustc")
    if target == "x86_64-unknown-linux-gnu":
        if target != host:
            raise ValueError(f"{target} requires a native build host; current Rust host is {host}")
        require_tool("readelf")
    elif target == "x86_64-pc-windows-msvc":
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
        return
    # Inspect our own ELF output; do not execute a foreign program with ldd.
    headers = run(["readelf", "-l", str(path)]).stdout
    dynamic = run(["readelf", "-d", str(path)]).stdout
    if "INTERP" in headers or "(NEEDED)" in dynamic:
        raise ValueError("Linux release server must be statically linked (ELF interpreter/dependencies found)")


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
                preflight(target, host)
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
