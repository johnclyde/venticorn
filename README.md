<!-- Modified for Venticorn: local development and usage instructions. -->
# Venticorn

Venticorn is an automated theorem prover with `.ac` source files, command-line verification, and a VS Code development extension.

Use this repository to develop the prover or editor integration, or to build them locally. Mathematical projects can live in their own library directories. The [extension guide](vscode/extension/README.md) describes editor setup; published server assets are not required when you configure a local build with `SERVER_PATH`.

## Build and check locally

Install Rust with Cargo, Node.js with npm, and Python 3.11 or newer for local tooling and protocol smoke tests. VS Code 1.82 or newer is needed only for the editor integration. Development checks have been run with Rust 1.86 and Node.js 22.

```sh
git clone https://github.com/johnclyde/venticorn.git
cd venticorn
cargo build --locked
cargo test --locked
npm --prefix vscode/extension ci
npm --prefix vscode/assistant ci
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

## Anonymous theorems and axioms

Theorem names are optional. Omitting a name keeps the proof obligation and avoids adding a named binding:

```acorn
theorem(value: Bool) { value or not value }
theorem<T>(value: T) { value = value }
theorem(value: Bool) { value -> value } by { value }
```

Arguments and type parameters stay within their declaration. Anonymous claims retain their source ranges for diagnostics and editor selection. If a claim cannot yet be printed as source code, the goal is labeled by its source line.

An `axiom` deliberately adds an assumption instead of a proof obligation, with or without a name. For example, this module verifies its theorem using the explicit assumption:

```acorn
let b: Bool = axiom
axiom { b }
theorem { b }
```

Axioms do not take `by` blocks. Use `theorem` when the declaration should be checked by proof search.

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

## Operators

Prefix minus uses the operand type's `neg` member, so `-a` has the same meaning as `a.neg`. A type supports arithmetic negation by defining `neg(self)`; the bundled `Int` type provides it. Subtraction remains a separate `sub` member, including expressions such as `a - -b`.

Member access and function application bind before prefix minus, which binds before multiplication and addition. Thus `-a.suc` negates the successor, while `(-a).suc` takes the successor of a negative value. Use `-(a * b)` to negate an entire product. Boolean `not` binds below comparisons and above `and` and `or`; use `not (b and c)` to negate the conjunction. Generated proof expressions preserve these groupings.

## Choose a library and use the CLI

A library is a directory containing `.ac` files. A compatible mathematical library is included at `vscode/extension/acornlib` and packaged with the editor, including its license and attribution. Select that path with `VENTICORN_LIBRARY` to try the bundled modules, or use your own library directory. Set `VENTICORN_LIBRARY` to choose it explicitly; an absolute path is recommended. Relative values resolve from the process working directory. An empty value or a path that is not a directory is an error.

Without that variable, Venticorn searches the working directory and each ancestor. At each level it accepts the directory itself if its name is `venticorn-library`, `acornlib`, or `acorn-library`; otherwise it checks children with those names in that order. For example, a `venticorn-library` beside this checkout is discovered when commands run from the checkout. Discovery does not use the directory in which the binary was built.

```sh
export VENTICORN_LIBRARY=/absolute/path/to/your/library

# Verify all modules, or one module without its .ac suffix.
cargo run --locked --release --bin verify
cargo run --locked --release --bin verify -- hello
cargo run --locked --release --bin verify -- path/to/proof.ac

# Search for the proposition on a one-based source line.
cargo run --locked --release --bin search -- hello 1

# Export proof-search examples for optional model training.
cargo run --locked --release --bin verify -- --dataset
```

Use dotted module names for subdirectories, such as `algebra.groups`, or a relative or absolute `.ac` file path. The `--module hello` form remains supported. A file outside the library can import from the selected library. `verify` exits unsuccessfully when loading or verification fails. `search` prints its outcome and is intended for interactive investigation. Release builds are recommended for larger libraries. The `fastdev` profile uses release optimization while keeping debug symbols for local debugging and profiling; ordinary release builds omit those symbols. For example, run `cargo build --locked --profile fastdev --bin profile_prover`.

The verifier rechecks every goal without a cache by default; `--no-cache` makes that choice explicit. Use `--cache` to reuse matching verified results and save completed builds. Use `--filtered` to recheck every goal with saved premise hints, falling back to full search when those hints are insufficient. These cache modes are mutually exclusive. Dataset builds always perform fresh full searches.

## Run the VS Code extension from source

Install the two npm dependency sets above, then launch VS Code from a terminal with the library selected:

```sh
export VENTICORN_LIBRARY=/absolute/path/to/your/library
code .
```

If an existing VS Code process does not inherit that environment, close it and launch it again from this terminal. Open this repository as the workspace and press F5 with **Launch Extension Host** selected. The prelaunch task builds the Rust server with the optimized `fastdev` profile and debug symbols, bundles the extension into `vscode/extension/build/extension/bundle.js`, and builds the proof-search UI into `vscode/extension/build/assistant`. The launch configuration sets `SERVER_PATH` to this checkout's `target/fastdev/venticornserver` (`venticornserver.exe` on Windows); the extension host inherits `VENTICORN_LIBRARY` from VS Code. The server is run in place and is excluded from the extension package.

In the new Extension Development Host window, open your library directory and an `.ac` file, or run **Venticorn: New Venticorn File** and save it as `hello.ac`. Saving a document runs verification. Untitled documents receive language support but do not issue file-based proof requests. Once the server starts, the Assistant opens beside the first active Acorn document, including an untitled document. It shows guidance until the file is saved and clears earlier proof results while changes are unsaved. Place the cursor on a proposition to inspect proof search. After closing the Assistant, use the acorn toolbar button or **Venticorn: Show Assistant** to reopen it. The `.ac` extension and language identifier remain compatible. Existing `acorn.displayInfoView`, `acorn.toggleInfoView`, `acorn.displaySearchPanel`, and `acorn.toggleSearchPanel` commands remain aliases for saved user keybindings.

The language server selects its library when the editor initializes the connection. `VENTICORN_LIBRARY` takes precedence, including when no workspace is open. Otherwise it discovers a library near the local workspace; if none is found, it uses the `acornlib` copy bundled in the extension. This also supports standalone `.ac` files in a window without a workspace. A supplied workspace never falls back to the server process's working directory. An invalid explicit library setting, invalid workspace path, unsupported workspace URI, or missing bundled library produces an initialization error.

The extension supplies its installation directory through `--extension-root` and its first local workspace folder through `--workspace-root`. Other clients may omit these flags and use the initialization workspace URI or `VENTICORN_LIBRARY`. Library paths are validated before the backend is created, so configuration failures remain visible through the editor protocol.

Repeated verification within one running server reuses completed proofs for unchanged modules and their verified dependencies. After an edit, earlier goals can also be reused when their complete source prefix, proof context and dependencies still match. Editing an enclosing proof block rechecks its child goals; changing an import or dependency rechecks the affected module. Failed goals are searched again; an interrupted build does not publish partial results. This cache stays in memory and is cleared when the server restarts.

With a library selected, the editor also supports standalone `.ac` files outside that library. Unsaved editor content takes precedence over disk content. Their imports resolve from the selected library. Opening or saving changed content refreshes dependent modules; closing a buffer discards its editor version and restores disk content for any remaining importers. Command-line verification still enumerates the selected library.

An initialization failure is shown once with its cause. The extension does not retry initialization or automatically restart a stopped server; correct the configuration and reload the editor window to try again. Error details remain in the language-client output channel.

The F5 build uses ONNX by default. For a heuristic-only editor session, add `--no-default-features` to the local `cargo build` task in `.vscode/tasks.json` before launching.

## Release preparation

See [the release guide](RELEASE.md) for synchronized versions, platform builds, local packaging, and explicit publication.

## Optional model training

See [the Python tooling instructions](python/README.md). Training requires separate Python dependencies, a generated dataset, and the CUDA-capable PyTorch setup used by the training configuration. Update `python/config.py` to point to your dataset before running the notebooks. These tools are not needed to verify theorems or use the editor.

## Current development layout

The default ONNX model is embedded in the executables at compile time, so inference does not need a model file or the original checkout at runtime. See [the model notes](files/models/README.md) before replacing the bundled model. If the embedded model cannot be initialized, the default scorer reports the error and uses the built-in heuristic. Dataset export still writes into the compilation checkout's `files/datasets` directory; keep that directory available when exporting training data.

The extension package includes generated build assets, bundled JavaScript dependencies, language definitions, artwork, and license notices. Validate the actual VSIX with `package.sh`; an npm package listing alone does not verify an installed VS Code extension.

The extension uses esbuild to bundle its code and runtime JavaScript dependencies. TypeScript still checks the source before bundling; lifecycle tests compile isolated modules into `build/test`, which is excluded from the package. The bundle preserves dependency license comments and includes `THIRD_PARTY_NOTICES.txt`.

The extension includes its compiled code and proof-search webview under `vscode/extension/build`. Build both before inspecting the package: `npm --prefix vscode/extension run build` and `npm --prefix vscode/assistant run build`. The Vite build clears only `build/assistant`, preserving the compiled extension code. The extension uses explicit `SERVER_PATH` first. Otherwise it looks in its global storage `bin` directory for `venticornserver-vVERSION-PLATFORM`, including `.exe` on Windows. The version must match the extension. If the matching server is absent, the extension downloads only that versioned asset from `johnclyde/venticorn` over HTTPS. It validates the response and size, follows bounded redirects to GitHub release hosts, and installs a completed temporary file atomically. Concurrent requests share one download and progress notification, and a cached version is reused without another notification. Known download sizes show percentage progress; unknown sizes show received bytes. If the asset has not been published or the network is unavailable, one error explains how to build locally and set `SERVER_PATH`; the extension does not retry automatically. The server needs a library directory, but its embedded model allows the executable to run after relocation. If you move the checkout, update any explicit executable or library paths used by your editor. Until matching server release assets are available, use a source build with `SERVER_PATH`.

License and attribution information is retained in [LICENSE](LICENSE) and [NOTICE](NOTICE).
