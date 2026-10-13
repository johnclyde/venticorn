<!-- Modified for Venticorn. -->
# Proof-scoring model

The bundled ONNX model ranks proof-search steps. It changes search order, not the logical inference rules. The default Rust build enables the `onnx` feature and loads the newest `model-*.onnx` file in this directory.

Run `cargo test --locked` to check the learned scorer and prover. Use `cargo test --locked --no-default-features` for the built-in heuristic without the native ONNX runtime. If a model cannot be loaded, the prover reports that it is using the built-in heuristic.
