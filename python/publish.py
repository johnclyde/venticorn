#!/usr/bin/env python3
"""Stage or explicitly upload already-built language servers to a GitHub release."""

import argparse
from pathlib import Path
import shutil
import subprocess
import tempfile

from version import update_version

REPOSITORY = "johnclyde/venticorn"
PLATFORMS = (
    ("linux-x64", "x86_64-unknown-linux-gnu", ""),
    ("win32-x64", "x86_64-pc-windows-msvc", ".exe"),
    ("darwin-arm64", "aarch64-apple-darwin", ""),
)


def release_plan(root):
    version = update_version(root)
    tag = "v" + version
    artifacts = []
    for platform, target, suffix in PLATFORMS:
        source = root / "target" / target / "release" / ("venticornserver" + suffix)
        if not source.is_file() or source.stat().st_size == 0:
            raise ValueError(f"Missing or empty server: {source}. Build this target with crossbuild.sh first.")
        artifacts.append((source, f"venticornserver-{tag}-{platform}{suffix}"))
    return tag, artifacts


def publish(root, mode):
    # Validate every target before staging or making any network request.
    tag, artifacts = release_plan(root)
    for source, name in artifacts:
        print(f"{source} -> {REPOSITORY} release {tag}: {name}")
    if mode == "dry-run":
        print("Dry run only. Use --stage to prepare files or --upload to upload to an existing release.")
        return
    if mode == "upload":
        # Upload never creates a release or overwrites an existing asset.
        subprocess.run(["gh", "release", "view", tag, "--repo", REPOSITORY], check=True)
    staging = root / "files/release" / tag
    staging.mkdir(parents=True, exist_ok=True)
    paths = []
    for source, name in artifacts:
        destination = staging / name
        with tempfile.NamedTemporaryFile(dir=staging, prefix=".staging-", delete=False) as stream:
            temporary = Path(stream.name)
        try:
            shutil.copyfile(source, temporary)
            temporary.replace(destination)
        finally:
            temporary.unlink(missing_ok=True)
        paths.append(destination)
    if mode == "upload":
        subprocess.run(["gh", "release", "upload", tag, "--repo", REPOSITORY, *map(str, paths)], check=True)
    else:
        print(f"Staged {len(paths)} servers in {staging}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--dry-run", action="store_true", help="validate and print the plan (default)")
    group.add_argument("--stage", action="store_true", help="copy assets into files/release without network access")
    group.add_argument("--upload", action="store_true", help="upload to an existing GitHub release; requires gh authentication")
    args = parser.parse_args()
    mode = "upload" if args.upload else "stage" if args.stage else "dry-run"
    try:
        publish(Path(__file__).resolve().parent.parent, mode)
    except (OSError, KeyError, TypeError, ValueError, subprocess.CalledProcessError) as error:
        parser.exit(1, f"Release assets: {error}\n")


if __name__ == "__main__":
    main()
