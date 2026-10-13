<!-- Modified for Venticorn. -->
# Proof-scoring model

The bundled ONNX model ranks proof-search steps. It changes search order, not the logical inference rules. The default Rust build enables the `onnx` feature and embeds `model-2024-09-25-15-33-10.onnx` into each executable at compile time. Running a built executable does not require this directory. Training a new model does not change the bundled default until the `include_bytes!` path in `src/ort_model.rs` is updated and the executable is rebuilt.

Run `cargo test --locked` to check the learned scorer and prover. Use `cargo test --locked --no-default-features` for the built-in heuristic without the native ONNX runtime. If a model cannot be loaded, the prover reports that it is using the built-in heuristic.
