<!-- Modified for Venticorn. -->
# Venticorn for VS Code

Venticorn verifies `.ac` files and displays proof-search results in the editor.

This extension is currently supported through the repository's local development workflow. Follow the [build and editor instructions](https://github.com/johnclyde/venticorn#run-the-vs-code-extension-from-source). The source workflow builds the extension, runs the language server from the checkout through `SERVER_PATH`, and bundles the proof-search UI into `build/search`. The server executable is not included in the extension package. The package includes compiled extension code, the bundled search UI, language definitions, and artwork. Build the extension and search UI before inspecting its contents with `npm pack --dry-run --ignore-scripts`.

The extension uses Apache-2.0 licensed Acorn source and artwork. See the included LICENSE and NOTICE files.
