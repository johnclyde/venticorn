use sha2::{Digest, Sha256};
use std::{env, fs, path::Path, process::Command};

fn frame(hash: &mut Sha256, bytes: &[u8]) {
    hash.update((bytes.len() as u64).to_le_bytes());
    hash.update(bytes);
}

fn source_files(directory: &Path, paths: &mut Vec<std::path::PathBuf>) {
    for entry in fs::read_dir(directory).expect("read checker source directory") {
        let path = entry.expect("read checker source entry").path();
        if path.is_dir() {
            source_files(&path, paths);
        } else if path.extension().is_some_and(|extension| extension == "rs") {
            paths.push(path);
        }
    }
}

fn main() {
    let mut hash = Sha256::new();
    frame(&mut hash, b"venticorn:compiled-checker:v1");
    let mut files = vec![
        "build.rs".into(),
        "Cargo.toml".into(),
        "Cargo.lock".into(),
        "files/models/model-2024-09-25-15-33-10.onnx".into(),
    ];
    source_files(Path::new("src"), &mut files);
    files.sort();
    println!("cargo:rerun-if-changed=src");
    for file in files {
        println!("cargo:rerun-if-changed={}", file.display());
        frame(&mut hash, file.as_os_str().as_encoded_bytes());
        frame(
            &mut hash,
            &fs::read(&file).expect("read checker identity input"),
        );
    }
    let mut configuration: Vec<_> = env::vars()
        .filter(|(name, _)| {
            name.starts_with("CARGO_FEATURE_")
                || name.starts_with("CARGO_CFG_")
                || matches!(name.as_str(), "TARGET" | "CARGO_ENCODED_RUSTFLAGS")
        })
        .collect();
    configuration.sort();
    for (name, value) in configuration {
        frame(&mut hash, name.as_bytes());
        frame(&mut hash, value.as_bytes());
    }
    let compiler = Command::new(env::var_os("RUSTC").expect("compiler path"))
        .arg("--version")
        .arg("--verbose")
        .output()
        .expect("compiler identity");
    assert!(compiler.status.success(), "compiler identity failed");
    frame(&mut hash, &compiler.stdout);
    println!("cargo:rustc-env=VENTICORN_CHECKER_ID={:x}", hash.finalize());
}
