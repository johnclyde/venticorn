#!/usr/bin/env python3
"""Build local release-server artifacts without installing tools or publishing."""

import argparse
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
TARGETS = {
    "x86_64-unknown-linux-gnu": ("linux-x64", "venticornserver"),
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
    # A fixed output path is part of the release-staging contract.
    env["CARGO_TARGET_DIR"] = str(ROOT / "target")
    output = ROOT / "target" / target / "release" / TARGETS[target][1]
    return command, env, output


def preflight(target, host):
    require_tool("cargo")
    require_tool("rustc")
    # Cross compilers and native runtime archives are outside this script's scope.
    if target != host:
        raise ValueError(f"{target} requires a native build host; current Rust host is {host}")
    require_tool("readelf")
    target_lib = Path(run(["rustc", "--print", "target-libdir", "--target", target]).stdout.strip())
    if not target_lib.is_dir():
        raise ValueError(f"Rust standard library is missing for {target}; install that target explicitly")


def validate_artifact(target, path):
    if not path.is_file():
        raise ValueError(f"build succeeded without the expected artifact: {path}")
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
