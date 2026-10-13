<!-- Modified for Venticorn. -->
# Venticorn for VS Code

Venticorn verifies `.ac` files and displays proof-search results in the editor.

This extension is currently supported through the repository's local development workflow. Follow the [build and editor instructions](https://github.com/johnclyde/venticorn#run-the-vs-code-extension-from-source). The source workflow builds the extension, runs the language server from the checkout through `SERVER_PATH`, and builds the neighboring search UI. The server executable is not included in the extension package. The package files list describes the generated extension assets; the search UI is not yet bundled in this directory.

The extension uses Apache-2.0 licensed Acorn source and artwork. See the included LICENSE and NOTICE files.
