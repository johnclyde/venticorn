<!-- Modified for Venticorn: local development and usage instructions. -->
# Venticorn

Venticorn is an automated theorem prover with `.ac` source files, command-line verification, and a VS Code development extension.

## Build and check locally

Install Rust with Cargo, Node.js with npm, and Python 3 for the protocol smoke tests. VS Code 1.82 or newer is needed only for the editor integration. Development checks have been run with Rust 1.86 and Node.js 22.

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

Use dotted module names for subdirectories, such as `algebra.groups`. `verify` exits unsuccessfully when loading or verification fails. `search` prints its outcome and is intended for interactive investigation. Release builds are recommended for larger libraries.

## Run the VS Code extension from source

Install the two npm dependency sets above, then launch VS Code from a terminal with the library selected:

```sh
export VENTICORN_LIBRARY=/absolute/path/to/your/library
code .
```

If an existing VS Code process does not inherit that environment, close it and launch it again from this terminal. Open this repository as the workspace and press F5 with **Launch Extension Host** selected. The prelaunch task builds the Rust release binaries, compiles the extension, and builds the proof-search UI. The launch configuration sets `SERVER_PATH` to this checkout's `target/release/language_server`; the extension host inherits `VENTICORN_LIBRARY` from VS Code.

In the new Extension Development Host window, open your library directory and an `.ac` file. Saving a document runs verification. Place the cursor on a proposition and use **Venticorn: Search Panel: Display** from the command palette to inspect proof search. The `.ac` extension and existing language and command identifiers remain compatible.

The language server selects its library when the editor initializes the connection. `VENTICORN_LIBRARY` takes precedence, including when no workspace is open. Without that override, discovery starts from the first workspace folder supplied by the editor, or its legacy root URI. A supplied workspace never falls back to the server process's working directory. Open a local workspace containing or neighboring a supported library directory, or set the override; missing libraries and unsupported workspace URIs produce an initialization error.

An initialization failure is shown once with its cause. The extension does not retry initialization or automatically restart a stopped server; correct the configuration and reload the editor window to try again. Error details remain in the language-client output channel.

The F5 build uses ONNX by default. For a heuristic-only editor session, add `--no-default-features` to the local `cargo build` task in `.vscode/tasks.json` before launching.

## Optional model training

See [the Python tooling instructions](python/README.md). Training requires separate Python dependencies, a generated dataset, and the CUDA-capable PyTorch setup used by the training configuration. Update `python/config.py` to point to your dataset before running the notebooks. These tools are not needed to verify theorems or use the editor.

## Current development layout

The model loader reads `files/models/model-*.onnx` from the checkout path embedded at compilation time and chooses the lexicographically latest filename. Dataset export likewise writes into that checkout's `files/datasets` directory. If the model cannot be loaded, the default scorer reports the error and uses the built-in heuristic.

The development extension expects the neighboring `vscode/search/dist` build and the configured `SERVER_PATH`. Keep the checkout and its assets available when running these development binaries; copying a binary or extension folder alone does not create a self-contained installation. Moving the checkout requires rebuilding. Source builds and the local workflow are currently the supported setup.

License and attribution information is retained in [LICENSE](LICENSE) and [NOTICE](NOTICE).
