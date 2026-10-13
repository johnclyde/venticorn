<!-- Modified for Venticorn: local development and usage instructions. -->
# Venticorn

Venticorn is an automated theorem prover with `.ac` source files, command-line verification, and a VS Code development extension.

## Build and check locally

Install Rust with Cargo, Node.js with npm, and Python 3.11 or newer for local tooling and protocol smoke tests. VS Code 1.82 or newer is needed only for the editor integration. Development checks have been run with Rust 1.86 and Node.js 22.

```sh
git clone https://github.com/johnclyde/venticorn.git
cd venticorn
cargo build --locked
cargo test --locked
npm --prefix vscode/extension ci
npm --prefix vscode/info ci
bash scripts/check.sh
```

The check script checks Rust formatting, runs the Rust tests with both scorers, builds the command-line tools, exercises the language-server protocol, and checks the editor startup lifecycle and UI build. All validation runs locally; this repository has no GitHub Actions workflows. Initial dependency installation needs network access.

ONNX proof scoring is enabled by default. The pinned native runtime and the included model support local inference without a Python installation. To build and test with the built-in heuristic scorer instead:

```sh
cargo build --locked --no-default-features
cargo test --locked --no-default-features
```

The heuristic uses the same proof machinery with a different search order. Its speed and ability to finish a search within the limits can differ from ONNX scoring. The `profile_scorer` binary requires the default `onnx` feature.

## Verify a first theorem

From the repository root, create an independent library directory and a theorem that needs no imports:

```sh
export VENTICORN_LIBRARY="$(mktemp -d)"
printf '%s\n' "$VENTICORN_LIBRARY"
cat > "$VENTICORN_LIBRARY/hello.ac" <<'EOF'
theorem identity(value: Bool) { value = value }
EOF
cargo run --locked --bin verify -- --module hello
cargo run --locked --bin search -- hello 1
```

Verification should report one successful goal, and search should report `Success!`. This directory can hold additional `.ac` modules. Keep the printed value of `VENTICORN_LIBRARY` if you want to reopen it in the editor. Add `--no-default-features` before `--bin` to run these commands with the heuristic scorer.

## Match expressions

Use `match` to define a value by constructor. For example, this complete module verifies with `verify`:

```acorn
inductive Choice {
    first
    second
}
let selected: Bool = match Choice.first {
    Choice.first { true }
    Choice.second { false }
}
theorem selected_is_true { selected }
```

Match expressions also work in `define` bodies. Include every constructor exactly once, with its full argument list, and give all cases the same result type. A constructor argument is bound by a simple name within that case; names cannot repeat within a pattern or shadow an existing binding. Structure values use their `Type.new(...)` constructor in patterns.

Proof normalization supports nested matches, surrounding quantifiers, comparisons, and function applications. Applying a lambda that contains a match is supported; passing an unapplied lambda containing a match as a higher-order value still reports an unsupported-normalization error. Generating match syntax in proof output is not yet implemented. Some quantified Boolean equalities remain beyond the current proof search. Standalone match statements split a proof into exhaustive constructor cases. Every case is verified, and only the disjunction of the case conclusions is available outside the statement. Select a claim inside any case to inspect its proof in the editor. Expression matches, such as the let binding above, are supported.

## Recursive definitions

A function may call itself when every recursive call uses a strict substructure of the same original argument. Matching a constructor exposes those smaller values. For example, this complete module defines addition and verifies its base equation:

```acorn
inductive Nat {
    zero
    suc(Nat)
}
define add(a: Nat, b: Nat) -> Nat {
    match a {
        Nat.zero { b }
        Nat.suc(pred) { add(pred, b).suc }
    }
}
theorem goal(n: Nat) { add(Nat.zero, n) = n }
```

The decreasing argument can be any argument, including a member function's receiver or a later member argument. Generic recursive functions are also supported. One fixed argument position must decrease on every call; alternating which argument decreases can form a loop and is rejected. Passing the recursive function itself as a value is rejected when its descent cannot be checked.

Recursive constructor fields must use the inductive type directly, such as `suc(Nat)`. A nested occurrence such as `Nat -> Bool` or `Bool -> Nat` is unsupported. Unrelated function fields remain allowed.

Passing the termination and type checks does not guarantee that proof search will establish every true theorem about the function. The base equation above and concrete recursive unfoldings are supported; some Boolean and higher-order claims remain beyond current proof search. A rejected termination check means the checker could not establish structural descent, not necessarily that the function loops.

## Choose a library and use the CLI

The library is a separate directory containing `.ac` files. Set `VENTICORN_LIBRARY` to choose it explicitly; an absolute path is recommended. Relative values resolve from the process working directory. An empty value or a path that is not a directory is an error.

Without that variable, Venticorn searches the working directory and each ancestor. At each level it accepts the directory itself if its name is `venticorn-library`, `acornlib`, or `acorn-library`; otherwise it checks children with those names in that order. For example, a `venticorn-library` beside this checkout is discovered when commands run from the checkout. Discovery does not use the directory in which the binary was built.

```sh
export VENTICORN_LIBRARY=/absolute/path/to/your/library

# Verify all modules, or one module without its .ac suffix.
cargo run --locked --release --bin verify
cargo run --locked --release --bin verify -- --module hello

# Search for the proposition on a one-based source line.
cargo run --locked --release --bin search -- hello 1

# Export proof-search examples for optional model training.
cargo run --locked --release --bin verify -- --dataset
```

Use dotted module names for subdirectories, such as `algebra.groups`. `verify` exits unsuccessfully when loading or verification fails. `search` prints its outcome and is intended for interactive investigation. Release builds are recommended for larger libraries. The `fastdev` profile uses release optimization while keeping debug symbols for local debugging and profiling; ordinary release builds omit those symbols. For example, run `cargo build --locked --profile fastdev --bin profile_prover`.

## Run the VS Code extension from source

Install the two npm dependency sets above, then launch VS Code from a terminal with the library selected:

```sh
export VENTICORN_LIBRARY=/absolute/path/to/your/library
code .
```

If an existing VS Code process does not inherit that environment, close it and launch it again from this terminal. Open this repository as the workspace and press F5 with **Launch Extension Host** selected. The prelaunch task builds the Rust server with the optimized `fastdev` profile and debug symbols, bundles the extension into `vscode/extension/build/extension/bundle.js`, and builds the proof-search UI into `vscode/extension/build/info`. The launch configuration sets `SERVER_PATH` to this checkout's `target/fastdev/venticornserver` (`venticornserver.exe` on Windows); the extension host inherits `VENTICORN_LIBRARY` from VS Code. The server is run in place and is excluded from the extension package.

In the new Extension Development Host window, open your library directory and an `.ac` file. Saving a document runs verification. Place the cursor on a proposition and use **Venticorn: Info View: Display** from the command palette to inspect proof search. The `.ac` extension and language identifier remain compatible. Existing `acorn.displaySearchPanel` and `acorn.toggleSearchPanel` commands remain aliases for saved user keybindings.

The language server selects its library when the editor initializes the connection. `VENTICORN_LIBRARY` takes precedence, including when no workspace is open. Without that override, discovery starts from the first workspace folder supplied by the editor, or its legacy root URI. A supplied workspace never falls back to the server process's working directory. Open a local workspace containing or neighboring a supported library directory, or set the override; missing libraries and unsupported workspace URIs produce an initialization error.

With a library selected, the editor also supports standalone `.ac` files outside that library. Unsaved editor content takes precedence over disk content. Their imports resolve from the selected library. Opening or saving changed content refreshes dependent modules; closing a buffer discards its editor version and restores disk content for any remaining importers. Command-line verification still enumerates the selected library.

An initialization failure is shown once with its cause. The extension does not retry initialization or automatically restart a stopped server; correct the configuration and reload the editor window to try again. Error details remain in the language-client output channel.

The F5 build uses ONNX by default. For a heuristic-only editor session, add `--no-default-features` to the local `cargo build` task in `.vscode/tasks.json` before launching.

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

On Windows, run `python python/crossbuild.py x86_64-pc-windows-msvc` in an MSVC developer shell with the Windows SDK available. The Python entrypoint does not require Bash.

For a cross-build, first provision an xwin-compatible SDK yourself and review its licensing. Set `XWIN_ROOT` to its absolute path; the script requires `crt/lib/x86_64`, `sdk/lib/um/x86_64`, and `sdk/lib/ucrt/x86_64` under that directory. It uses `lld-link`, or the executable named by `CARGO_TARGET_X86_64_PC_WINDOWS_MSVC_LINKER`. No user-specific linker paths are stored in the repository.

```sh
export XWIN_ROOT=/absolute/path/to/your/windows-sdk
./crossbuild.sh --plan x86_64-pc-windows-msvc
./crossbuild.sh x86_64-pc-windows-msvc
```

The output is `target/x86_64-pc-windows-msvc/release/venticornserver.exe`. The build requests a static C runtime and verifies the output is x64 PE; it does not claim the file has no Windows system-library dependencies. Test the resulting server on Windows before release. Cross SDKs and ONNX runtime compatibility require platform validation and are not installed or repaired by this script.

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

`package.sh` checks synchronized versions, rebuilds the extension and search UI, and creates `files/release/venticorn-extension-VERSION.vsix`. It then unpacks that archive, verifies runtime dependencies and license notices, excludes node_modules, test modules, development tools, and server binaries, and loads the compiled extension with a VS Code host stub. The command does not publish to a marketplace. Install the two project npm dependency sets before running it, as described above. Generated release files are ignored by Git.

## Optional model training

See [the Python tooling instructions](python/README.md). Training requires separate Python dependencies, a generated dataset, and the CUDA-capable PyTorch setup used by the training configuration. Update `python/config.py` to point to your dataset before running the notebooks. These tools are not needed to verify theorems or use the editor.

## Current development layout

The default ONNX model is embedded in the executables at compile time, so inference does not need a model file or the original checkout at runtime. See [the model notes](files/models/README.md) before replacing the bundled model. If the embedded model cannot be initialized, the default scorer reports the error and uses the built-in heuristic. Dataset export still writes into the compilation checkout's `files/datasets` directory; keep that directory available when exporting training data.

The extension package includes generated build assets, bundled JavaScript dependencies, language definitions, artwork, and license notices. Validate the actual VSIX with `package.sh`; an npm package listing alone does not verify an installed VS Code extension.

The extension uses esbuild to bundle its code and runtime JavaScript dependencies. TypeScript still checks the source before bundling; lifecycle tests compile isolated modules into `build/test`, which is excluded from the package. The bundle preserves dependency license comments and includes `THIRD_PARTY_NOTICES.txt`.

The extension includes its compiled code and proof-search webview under `vscode/extension/build`. Build both before inspecting the package: `npm --prefix vscode/extension run build` and `npm --prefix vscode/info run build`. The Vite build clears only `build/info`, preserving the compiled extension code. The extension uses explicit `SERVER_PATH` first. Otherwise it looks in its global storage `bin` directory for `venticornserver-vVERSION-PLATFORM`, including `.exe` on Windows. The version must match the extension. If the matching server is absent, the extension downloads only that versioned asset from `johnclyde/venticorn` over HTTPS. It validates the response and size, follows bounded redirects to GitHub release hosts, and installs a completed temporary file atomically. Concurrent requests share one download and progress notification, and a cached version is reused without another notification. Known download sizes show percentage progress; unknown sizes show received bytes. If the asset has not been published or the network is unavailable, one error explains how to build locally and set `SERVER_PATH`; the extension does not retry automatically. The server needs a library directory, but its embedded model allows the executable to run after relocation. If you move the checkout, update any explicit executable or library paths used by your editor. Until matching server release assets are available, use a source build with `SERVER_PATH`.

License and attribution information is retained in [LICENSE](LICENSE) and [NOTICE](NOTICE).
