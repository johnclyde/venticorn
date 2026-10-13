<!-- Modified for Venticorn: editor setup, first proof, and library selection. -->
# Venticorn for VS Code

Venticorn verifies `.ac` files and displays proof-search results in the editor. It includes language highlighting, a proof assistant, and a mathematical library with natural numbers, integers, and divisibility.

## Try a first proof

Run **Venticorn: New Venticorn File** from the command palette, or open an existing `.ac` file.
Untitled documents use the right language mode; verification and proof search begin after saving.
Once the language server is available, save a file named `hello.ac` containing:

```acorn
theorem identity(value: Bool) { value = value }
```

Saving runs verification. Once the server starts, the Assistant opens beside the first visible saved
proof file without moving focus out of the editor. Place the cursor on the proposition to inspect its
proof-search result or insert generated proof code when available. Saved `.ac` files work even outside
a workspace; imports use the selected library.

If you close the Assistant, reopen it with the small acorn button in the editor title bar,
**Venticorn: Assistant: Display**, or **Ctrl+Enter** (**Cmd+Enter** on macOS). It stays closed until you
reopen it or reload the editor window.

## Language server setup

The server executable is separate from the extension package. `SERVER_PATH` takes precedence; otherwise the extension reuses a matching cached server or downloads the exact extension version from `johnclyde/venticorn` releases. Packaged server platforms are Linux x64, Windows x64, and macOS Apple silicon.

If that release is unavailable, build the server locally and set `SERVER_PATH` to its absolute path before launching VS Code. Follow the [build and editor instructions](https://github.com/johnclyde/venticorn#run-the-vs-code-extension-from-source) for the source workflow and F5 development host. Reload VS Code after correcting setup; failed downloads or initialization are reported once and are not retried automatically. Setup details remain in the **Venticorn Extension** output channel, and server details in **Venticorn Language Server**.

## Library selection

The extension includes a compatible library under `acornlib`. Set `VENTICORN_LIBRARY` before launching VS Code to select a different library explicitly. Otherwise the server discovers a library near the local workspace, then falls back to the bundled copy. No workspace is required to use that fallback. An empty or invalid explicit setting is an error rather than an instruction to use another library.

For command-line use and supported language features, see the [development guide](https://github.com/johnclyde/venticorn#choose-a-library-and-use-the-cli). Build and inspect a local VSIX with the repository's `package.sh`; this rebuilds the extension and Assistant and validates their packaged assets without publishing.

The extension includes Apache-2.0 licensed Acorn source, artwork, and mathematical library files. See the included LICENSE and NOTICE files and the library's own license and attribution.
