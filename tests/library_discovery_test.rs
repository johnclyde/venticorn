use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT_DIRECTORY: AtomicUsize = AtomicUsize::new(0);

struct TestDirectory(PathBuf);

impl TestDirectory {
    fn new() -> Self {
        let id = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("venticorn_discovery_{}_{}", std::process::id(), id));
        fs::create_dir(&path).expect("create test directory");
        Self(path)
    }

    fn library(&self, name: &str, theorem: &str) -> PathBuf {
        let path = self.0.join(name);
        fs::create_dir_all(&path).unwrap();
        fs::write(path.join("main.ac"), theorem).unwrap();
        path
    }

    fn verify(&self, working_dir: &Path) -> Command {
        let mut command = Command::new(env!("CARGO_BIN_EXE_verify"));
        command
            .current_dir(working_dir)
            .env_remove("VENTICORN_LIBRARY")
            .args(["--module", "main"]);
        command
    }
}

impl Drop for TestDirectory {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn assert_success(output: Output) {
    assert!(
        output.status.success(),
        "stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(String::from_utf8_lossy(&output.stdout).contains("1/1 OK"));
}

#[test]
fn discovers_compatible_library_names_from_working_directory() {
    for name in ["venticorn-library", "acornlib", "acorn-library"] {
        let directory = TestDirectory::new();
        let library = directory.library(name, "theorem trivial { true }");
        let checkout = directory.0.join("checkout/src");
        fs::create_dir_all(&checkout).unwrap();
        assert_success(directory.verify(&checkout).output().unwrap());

        let nested = library.join("nested");
        fs::create_dir(&nested).unwrap();
        assert_success(directory.verify(&nested).output().unwrap());
    }
}

#[test]
fn discovery_prefers_venticorn_name_at_the_same_location() {
    let directory = TestDirectory::new();
    directory.library("acornlib", "theorem impossible { false }");
    directory.library("venticorn-library", "theorem trivial { true }");

    assert_success(directory.verify(&directory.0).output().unwrap());
}

#[test]
fn explicit_library_overrides_discovery() {
    let directory = TestDirectory::new();
    directory.library("venticorn-library", "theorem trivial { true }");
    let selected = directory.library("selected", "theorem impossible { false }");

    let output = directory
        .verify(&directory.0)
        .env("VENTICORN_LIBRARY", selected)
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&output.stdout).contains("could not be verified"));
}

#[test]
fn relative_override_uses_the_working_directory() {
    let directory = TestDirectory::new();
    directory.library("selected", "theorem trivial { true }");
    let checkout = directory.0.join("checkout");
    fs::create_dir(&checkout).unwrap();

    assert_success(
        directory
            .verify(&checkout)
            .env("VENTICORN_LIBRARY", "../selected")
            .output()
            .unwrap(),
    );
}

#[test]
fn invalid_override_never_falls_back_to_a_discovered_library() {
    let directory = TestDirectory::new();
    directory.library("venticorn-library", "theorem trivial { true }");
    fs::write(directory.0.join("file"), "not a directory").unwrap();

    for value in ["missing", "file", ""] {
        let output = directory
            .verify(&directory.0)
            .env("VENTICORN_LIBRARY", value)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(1));
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("VENTICORN_LIBRARY"), "{stderr}");
        assert!(!stderr.contains("panicked"), "{stderr}");
    }
}

#[test]
fn imported_parse_error_has_failure_exit_status() {
    let directory = TestDirectory::new();
    let library = directory.library("selected", "import broken");
    fs::write(library.join("broken.ac"), "theorem unfinished {").unwrap();

    let output = directory
        .verify(&directory.0)
        .env("VENTICORN_LIBRARY", library)
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&output.stdout).contains("Build failed."));
}

#[test]
fn verify_help_does_not_require_a_library() {
    let output = Command::new(env!("CARGO_BIN_EXE_verify"))
        .env("VENTICORN_LIBRARY", "")
        .arg("--help")
        .output()
        .unwrap();
    assert!(output.status.success());
    assert!(String::from_utf8_lossy(&output.stdout).contains("--module"));
}

#[test]
fn search_uses_the_explicit_library() {
    let directory = TestDirectory::new();
    let library = directory.library("selected", "theorem trivial { true }");
    let output = Command::new(env!("CARGO_BIN_EXE_search"))
        .current_dir(&directory.0)
        .env("VENTICORN_LIBRARY", library)
        .args(["main", "1"])
        .output()
        .unwrap();

    assert!(output.status.success());
    assert!(String::from_utf8_lossy(&output.stdout).contains("Success!"));
}

#[test]
fn search_and_profiling_report_invalid_library_without_panicking() {
    for (binary, args) in [
        (env!("CARGO_BIN_EXE_search"), vec!["main", "1"]),
        (env!("CARGO_BIN_EXE_profile_prover"), vec![]),
    ] {
        let output = Command::new(binary)
            .env("VENTICORN_LIBRARY", "")
            .args(args)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(1));
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("VENTICORN_LIBRARY"), "{stderr}");
        assert!(!stderr.contains("panicked"), "{stderr}");
    }
}

#[test]
fn discovered_library_paths_can_construct_an_external_project() {
    let directory = TestDirectory::new();
    let library = directory.library("acornlib", "theorem identity { true }");
    let path = venticorn::project::Project::find_local_library(&directory.0)
        .unwrap()
        .unwrap();
    assert_eq!(path, library.canonicalize().unwrap());
    let mut project = venticorn::project::Project::from_library_root(path).unwrap();
    assert!(project.add_target_by_name("main"));
}

#[test]
fn explicit_project_roots_and_discovery_starts_must_be_directories() {
    let directory = TestDirectory::new();
    let file = directory.0.join("acornlib");
    fs::write(&file, "not a library").unwrap();
    assert!(venticorn::project::Project::find_local_library(&file).is_err());
    assert!(venticorn::project::Project::from_library_root(file).is_err());
    assert!(venticorn::project::Project::from_library_root(directory.0.join("missing")).is_err());
}
