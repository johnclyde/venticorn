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
npm --prefix vscode/search ci
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

If an existing VS Code process does not inherit that environment, close it and launch it again from this terminal. Open this repository as the workspace and press F5 with **Launch Extension Host** selected. The prelaunch task builds the Rust server with the optimized `fastdev` profile and debug symbols, compiles the extension into `vscode/extension/build/extension`, and builds the proof-search UI into `vscode/extension/build/search`. The launch configuration sets `SERVER_PATH` to this checkout's `target/fastdev/venticornserver` (`venticornserver.exe` on Windows); the extension host inherits `VENTICORN_LIBRARY` from VS Code. The server is run in place and is excluded from the extension package.

In the new Extension Development Host window, open your library directory and an `.ac` file. Saving a document runs verification. Place the cursor on a proposition and use **Venticorn: Search Panel: Display** from the command palette to inspect proof search. The `.ac` extension and existing language and command identifiers remain compatible.

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

The local build script currently supports `x86_64-unknown-linux-gnu` on a native Linux x64 Rust host. It builds only the server, uses locked dependencies, and puts the result in `target/x86_64-unknown-linux-gnu/release/venticornserver`. An explicit target build scopes the static C runtime flags to that target. The script checks its ELF headers with `readelf` and rejects a Linux executable with an interpreter or shared-library dependencies.

```sh
./crossbuild.sh --plan x86_64-unknown-linux-gnu
./crossbuild.sh x86_64-unknown-linux-gnu
# Optional heuristic scorer; it uses the same artifact path.
./crossbuild.sh --no-default-features x86_64-unknown-linux-gnu
```

`--plan` prints commands and paths without building. A real build requires Cargo, the target's Rust standard library, native development/linker tools, and `readelf` from binutils. Dependencies must already be cached for an offline build; otherwise Cargo and the ONNX runtime build may need network access. Set `CARGO_NET_OFFLINE=true` to require cached dependencies. The script never installs toolchains, downloads SDKs, or publishes. Other host/target combinations fail with a configuration error.

## Coordinated releases

Every release pairs a language server and an extension at the same version, even when only one component changed. Prepare them from the same reviewed, merged revision. Run local checks, build each supported server target, and inspect the extension package before publishing anything.

Publish and verify the server assets before publishing the extension that requests that version. Use a release tag of `v` followed by `VERSION`; server assets are named `venticornserver-vVERSION-linux-x64`, `venticornserver-vVERSION-win32-x64.exe`, and `venticornserver-vVERSION-darwin-arm64`, replacing `VERSION` with its actual value. An extension-only release could otherwise request a server artifact that does not exist. Local build and version commands never create tags, releases, or marketplace uploads.

## Optional model training

See [the Python tooling instructions](python/README.md). Training requires separate Python dependencies, a generated dataset, and the CUDA-capable PyTorch setup used by the training configuration. Update `python/config.py` to point to your dataset before running the notebooks. These tools are not needed to verify theorems or use the editor.

## Current development layout

The default ONNX model is embedded in the executables at compile time, so inference does not need a model file or the original checkout at runtime. See [the model notes](files/models/README.md) before replacing the bundled model. If the embedded model cannot be initialized, the default scorer reports the error and uses the built-in heuristic. Dataset export still writes into the compilation checkout's `files/datasets` directory; keep that directory available when exporting training data.

The extension manifest includes generated build assets, language definitions, artwork, and license notices in its package file list. You can inspect that list locally with `(cd vscode/extension && npm pack --dry-run --ignore-scripts)`; this does not publish a package.

The extension includes its compiled code and proof-search webview under `vscode/extension/build`. Build both before inspecting the package: `npm --prefix vscode/extension run compile` and `npm --prefix vscode/search run build`. The Vite build clears only `build/search`, preserving the compiled extension code. The language server requires the configured `SERVER_PATH` and a library directory, but its embedded model allows the executable to run after relocation. If you move the checkout, update any explicit executable or library paths used by your editor. Source builds and the local workflow are currently the supported setup.

License and attribution information is retained in [LICENSE](LICENSE) and [NOTICE](NOTICE).
