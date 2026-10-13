<!-- Modified for Venticorn: local release preparation and platform validation. -->
# Releasing Venticorn

Run these commands from the repository root. See [the development guide](README.md) for prerequisites and local checks.

## Release platforms

The extension logs the Node.js platform and architecture when it activates, so a server build can be matched to the editor host. Release targets are Linux x64 (`linux-x64`), Windows x64 (`win32-x64`), and macOS Apple silicon (`darwin-arm64`). Source builds remain available for local development; a platform label alone does not mean a release artifact has been built or tested.

## Release versions

The server and extension share one `major.minor.patch` version, recorded in the root `VERSION` file. Check that `VERSION`, the Rust and extension manifests, and their lockfiles agree, or update them together, using the dependency-free Python tool:

```sh
python3 python/version.py
python3 python/version.py 0.1.1
```

The update command changes local files only. Review its diff and run `bash scripts/check.sh` before committing a version change. A mismatched manifest or lockfile causes the command to fail before writing anything; repair the inconsistency deliberately before retrying. The private webview and optional training package are not separately released through this tool.

## Local release builds

The local build script supports the three release targets with the platform setup below. With no target arguments, it chooses the Rust host target; unsupported hosts fail clearly. Linux x64 builds require a native Linux x64 Rust host. It builds only the server, uses locked dependencies, and puts the result in `target/x86_64-unknown-linux-gnu/release/venticornserver`. An explicit target build scopes the static C runtime flags to that target. The script checks its ELF headers with `readelf` and rejects a Linux executable with an interpreter or shared-library dependencies.

```sh
./crossbuild.sh --plan x86_64-unknown-linux-gnu
./crossbuild.sh x86_64-unknown-linux-gnu
# Optional heuristic scorer; it uses the same artifact path.
./crossbuild.sh --no-default-features x86_64-unknown-linux-gnu
```

`--plan` prints commands and paths without building. A real build requires Cargo, the target's Rust standard library, native development/linker tools, and `readelf` from binutils. Dependencies must already be cached for an offline build; otherwise Cargo and the ONNX runtime build may need network access. Set `CARGO_NET_OFFLINE=true` to require cached dependencies. The script never installs toolchains, downloads SDKs, or publishes. Unconfigured host/target combinations fail with a configuration error.

### Toolchains and target names

Use these complete Rust triples when preparing release hosts:

| Release platform | Rust target | Host prerequisites |
| --- | --- | --- |
| Linux x64 | `x86_64-unknown-linux-gnu` | Native x64 Linux compiler, static C/C++ runtime archives, binutils |
| Windows x64 | `x86_64-pc-windows-msvc` | MSVC linker and Windows SDK, or an explicitly configured cross-toolchain |
| macOS Apple silicon | `aarch64-apple-darwin` | Xcode Command Line Tools and macOS SDK, or an explicitly configured cross-toolchain |

Install a missing Rust standard library explicitly with `rustup target add TARGET`, substituting the chosen triple. Rust's target standard library does not install the platform linker, C/C++ libraries, or SDK. Keep SDK locations in your local environment; repository configuration must not assume a particular home directory or silently accept SDK licenses. The target table describes the release contract, not completed platform validation.

### Windows x64 builds

On Windows, run `python python/crossbuild.py x86_64-pc-windows-msvc` in an MSVC developer shell with the Windows SDK and `dumpbin` available. The Python entrypoint does not require Bash. ONNX builds also require an explicit `ORT_LIB_LOCATION` pointing to a static ONNX Runtime 1.19.2 build compatible with the pinned `ort` and `ort-sys` crates. Build that runtime with its `--enable_msvc_static_runtime` option and keep its dependency archives available; do not mix `/MD` runtime objects into a `/MT` build. See the [ONNX Runtime build instructions](https://onnxruntime.ai/docs/build/inferencing.html) and [Microsoft CRT library reference](https://learn.microsoft.com/en-us/cpp/c-runtime-library/crt-library-features).

For example, in PowerShell after preparing that runtime:

```powershell
$env:ORT_LIB_LOCATION = "C:\build\onnxruntime\build\Windows"
python python/crossbuild.py x86_64-pc-windows-msvc
# A heuristic-only build does not require ONNX Runtime:
python python/crossbuild.py --no-default-features x86_64-pc-windows-msvc
```

The helper uses static-runtime flags only for this explicit target, preserves the configured SDK paths, and rejects a request to prefer dynamic ONNX linking.

For a cross-build, first provision an xwin-compatible SDK yourself and review its licensing. Set `XWIN_ROOT` to its absolute path; the script requires `crt/lib/x86_64`, `sdk/lib/um/x86_64`, and `sdk/lib/ucrt/x86_64` under that directory. It uses `lld-link`, or the executable named by `CARGO_TARGET_X86_64_PC_WINDOWS_MSVC_LINKER`. `dumpbin` or `llvm-readobj` must also be available to inspect imported libraries. ONNX cross-builds require the same explicit target-compatible static runtime. No user-specific linker paths are stored in the repository.

```sh
export XWIN_ROOT=/absolute/path/to/your/windows-sdk
./crossbuild.sh --plan x86_64-pc-windows-msvc
./crossbuild.sh x86_64-pc-windows-msvc
```

The output is `target/x86_64-pc-windows-msvc/release/venticornserver.exe`. The build requests a static C runtime, verifies x64 PE format, and inspects normal and delay-load imports. It rejects ONNX Runtime and C/C++ runtime DLL dependencies, while allowing Windows system DLLs. Missing dependency inspection is an error. This checks direct imports, not DLLs loaded indirectly at runtime. Test the resulting server on Windows before release. Cross SDKs and ONNX runtime compatibility require platform validation and are not installed or repaired by this script.

### macOS Apple silicon builds

On macOS with Xcode Command Line Tools installed, build the ARM64 server with:

```sh
./crossbuild.sh --plan aarch64-apple-darwin
./crossbuild.sh aarch64-apple-darwin
# On an Apple silicon Rust host, this selects the same target:
./crossbuild.sh
```

For a cross-build from another operating system, install `cargo-zigbuild` and Zig explicitly, supply a macOS SDK you are licensed to use, and set `SDKROOT` to its absolute path. The script requires SDK libraries and frameworks and the target Rust standard library before invoking `cargo zigbuild`. It never obtains or redistributes an SDK.

The output is `target/aarch64-apple-darwin/release/venticornserver`. macOS uses its system runtime rather than Linux static-runtime flags. The script checks ARM64 Mach-O format and rejects dynamic dependencies outside `/usr/lib` and `/System/Library`. These checks also work on a foreign build host. Run the language-server protocol tests on macOS before release; format and linkage inspection alone cannot validate runtime compatibility.

Before creating a release, merge and review the version change, run the local checks, then build and validate each platform artifact. A successful `--plan` is only a command preview. It is not evidence that a cross-toolchain can link or that a foreign executable runs.

## Coordinated releases

Every release pairs a language server and an extension at the same version, even when only one component changed. Prepare them from the same reviewed, merged revision. Run local checks, build each supported server target, and inspect the extension package before publishing anything.

Publish and verify the server assets before publishing the extension that requests that version. Use a release tag of `v` followed by `VERSION`; server assets are named `venticornserver-vVERSION-linux-x64`, `venticornserver-vVERSION-win32-x64.exe`, and `venticornserver-vVERSION-darwin-arm64`, replacing `VERSION` with its actual value. An extension-only release could otherwise request a server artifact that does not exist. Local build and version commands never create tags, releases, or marketplace uploads.

## Prepare release artifacts locally

Build all three server targets and the local VSIX with `package.sh` first. The upload helper checks the complete set before doing anything, and uses the exact versioned asset names expected by the extension:

```sh
./publish.sh --dry-run   # Default: validate paths and print the upload plan.
./publish.sh --stage     # Copy the servers and VSIX into files/release/vVERSION.
```

After deliberately creating a release with the matching tag, `./publish.sh --upload` uploads the staged assets to `johnclyde/venticorn` using authenticated GitHub CLI access. It does not create releases or replace existing assets. Version checks, missing or empty artifacts, corrupt VSIX archives, and mismatched extension identities stop the command before any upload. The VSIX is included as a GitHub release asset; these commands do not publish it to the VS Code Marketplace.

Build a local VSIX with Node.js 22 and the pinned packaging tool:

```sh
VSCE_TOOLS="$(mktemp -d)"
npm install --prefix "$VSCE_TOOLS" @vscode/vsce@4.0.0 --no-audit --no-fund
VSCE="$VSCE_TOOLS/node_modules/.bin/vsce" ./package.sh
```

`package.sh` checks synchronized versions, rebuilds the extension and search UI, and creates `files/release/venticorn-extension-VERSION.vsix`. It then unpacks that archive, verifies runtime dependencies and license notices, excludes node_modules, test modules, development tools, and server binaries, and loads the compiled extension with a VS Code host stub. The command does not publish to a marketplace. Install the two project npm dependency sets before running it, as described in [the development guide](README.md). Generated release files are ignored by Git.
