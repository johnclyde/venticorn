<!-- Modified for Venticorn. -->
# Venticorn for VS Code

Venticorn verifies `.ac` files and displays proof-search results in the editor.

This extension is currently supported through the repository's local development workflow. Follow the [build and editor instructions](https://github.com/johnclyde/venticorn#run-the-vs-code-extension-from-source). The source workflow builds the extension, runs the language server from the checkout through `SERVER_PATH`, and bundles the proof-search UI into `build/info`. The server executable is not included in the extension package. `SERVER_PATH` takes precedence; otherwise the extension checks its global storage for a matching versioned server. If no cached server exists, the extension downloads the matching version from `johnclyde/venticorn` releases. Supported packaged platforms are Linux x64, Windows x64, and macOS Apple silicon. Until the matching release asset has been published, or if a download fails, follow the local build instructions and reload VS Code with `SERVER_PATH` set. Download and initialization failures appear once; the extension does not retry or restart automatically. The package includes an esbuild extension bundle, retained dependency licenses, bundled JavaScript dependencies, the bundled search UI, language definitions, artwork, and license notices. Use the repository's `package.sh` command to build and validate a local VSIX.

The extension uses Apache-2.0 licensed Acorn source and artwork. See the included LICENSE and NOTICE files.
