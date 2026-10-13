#!/usr/bin/env python3
"""Stage or explicitly upload already-built language servers and their extension to a GitHub release."""

import argparse
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import zipfile
from xml.etree import ElementTree

from version import update_version

REPOSITORY = "johnclyde/venticorn"
PLATFORMS = (
    ("linux-x64", "x86_64-unknown-linux-gnu", ""),
    ("win32-x64", "x86_64-pc-windows-msvc", ".exe"),
    ("darwin-arm64", "aarch64-apple-darwin", ""),
)


def extension_asset(root, version):
    source = root / "files/release" / f"venticorn-extension-{version}.vsix"
    if not source.is_file() or source.stat().st_size == 0:
        raise ValueError(f"Missing or empty extension: {source}. Build it with package.sh first.")
    expected = json.loads((root / "vscode/extension/package.json").read_text())
    try:
        with zipfile.ZipFile(source) as archive:
            package = json.loads(archive.read("extension/package.json"))
            manifest = ElementTree.fromstring(archive.read("extension.vsixmanifest"))
            identities = [element for element in manifest.iter() if element.tag.rsplit("}", 1)[-1] == "Identity"]
            if len(identities) != 1:
                raise ValueError("VSIX must contain exactly one extension identity")
            identity = identities[0]
            for key, attribute in (("name", "Id"), ("publisher", "Publisher"), ("version", "Version")):
                if not expected.get(key) or package.get(key) != expected[key] or identity.get(attribute) != expected[key]:
                    raise ValueError(f"VSIX {key} differs from the current extension manifest; rebuild with package.sh")
            if package["version"] != version:
                raise ValueError("VSIX version differs from the release version")
            # Validate the entire archive before staging or making a network request.
            bad_member = archive.testzip()
            if bad_member:
                raise ValueError(f"Corrupt VSIX member: {bad_member}")
    except (zipfile.BadZipFile, ElementTree.ParseError, KeyError) as error:
        raise ValueError(f"Invalid extension package: {error}") from error
    return source, source.name


def release_plan(root):
    version = update_version(root)
    tag = "v" + version
    artifacts = []
    for platform, target, suffix in PLATFORMS:
        source = root / "target" / target / "release" / ("venticornserver" + suffix)
        if not source.is_file() or source.stat().st_size == 0:
            raise ValueError(f"Missing or empty server: {source}. Build this target with crossbuild.sh first.")
        artifacts.append((source, f"venticornserver-{tag}-{platform}{suffix}"))
    artifacts.append(extension_asset(root, version))
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
        print(f"Staged {len(paths)} release assets in {staging}")


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
