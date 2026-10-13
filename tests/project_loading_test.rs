// Modified for Venticorn.

use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

use venticorn::builder::BuildStatus;
use venticorn::module::ModuleRef;
use venticorn::project::Project;

static NEXT_DIRECTORY: AtomicUsize = AtomicUsize::new(0);

struct TestDirectory(PathBuf);

impl TestDirectory {
    fn new() -> Self {
        let id = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("venticorn_loading_{}_{}", std::process::id(), id));
        fs::create_dir(&path).expect("create test directory");
        Self(path)
    }

    fn project(&self) -> Project {
        Project::new(self.0.to_str().unwrap())
    }

    fn write(&self, name: &str, content: &str) {
        fs::write(self.0.join(name), content).expect("write test module");
    }
}

impl Drop for TestDirectory {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn missing_target_prevents_proving_other_targets() {
    let directory = TestDirectory::new();
    directory.write("zvalid.ac", "theorem trivial { true }");
    let mut project = directory.project();
    assert!(!project.add_target_by_name("amissing"));
    assert!(project.add_target_by_name("zvalid"));

    let (status, events) = project.sync_build();
    assert_eq!(status, BuildStatus::Error);
    assert!(events.iter().any(|event| event
        .log_message
        .as_deref()
        .is_some_and(|message| message.contains("amissing is not loaded"))));
    assert!(events.iter().all(|event| event.diagnostic.is_none()));
}

#[test]
fn missing_root_reports_discovery_error() {
    let directory = TestDirectory::new();
    let missing = directory.0.join("missing");
    let mut project = Project::new(missing.to_str().unwrap());
    let error = project.add_all_targets().unwrap_err();
    assert!(error.to_string().contains("missing"));
}

#[test]
fn invalid_module_filename_reports_error_instead_of_panicking() {
    let directory = TestDirectory::new();
    directory.write("invalid-name.ac", "theorem trivial { true }");
    let error = directory.project().add_all_targets().unwrap_err();
    assert!(error
        .to_string()
        .contains("invalid character in module name"));
}

#[test]
fn discovery_only_skips_named_problems_subdirectories() {
    let directory = TestDirectory::new();
    let root = directory.0.join("problems_project");
    fs::create_dir_all(root.join("problems")).unwrap();
    fs::write(root.join("main.ac"), "theorem trivial { true }").unwrap();
    fs::write(root.join("problems.ac"), "theorem trivial { true }").unwrap();
    fs::write(root.join("problems/broken.ac"), "theorem unfinished {").unwrap();
    let mut project = Project::new(root.to_str().unwrap());

    project.add_all_targets().unwrap();

    assert!(project
        .get_env_by_ref(&ModuleRef::Name("main".to_string()))
        .is_some());
    assert!(project
        .get_env_by_ref(&ModuleRef::Name("problems".to_string()))
        .is_some());
    assert!(project
        .get_env_by_ref(&ModuleRef::Name("problems.broken".to_string()))
        .is_none());
    assert_eq!(project.sync_build().0, BuildStatus::Good);
}

#[test]
fn imported_parse_error_fails_the_build() {
    let directory = TestDirectory::new();
    directory.write("broken.ac", "theorem unfinished {");
    directory.write("main.ac", "import broken");
    let mut project = directory.project();
    assert!(project.add_target_by_name("main"));

    // The dependency is not itself a target, so its error must propagate through main.
    let (status, _) = project.sync_build();
    assert_eq!(status, BuildStatus::Error);
}

#[test]
fn unprovable_goal_is_not_a_successful_build() {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", "theorem impossible { false }");

    let (status, _) = project.sync_build();
    assert_eq!(status, BuildStatus::Warning);
}

#[test]
fn verified_goal_is_a_successful_build() {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", "theorem trivial { true }");

    let (status, _) = project.sync_build();
    assert_eq!(status, BuildStatus::Good);
}

#[test]
fn verify_exits_with_failure_for_a_missing_target() {
    let directory = TestDirectory::new();
    let module = format!("venticorn_missing_module_{}", std::process::id());
    let output = Command::new(env!("CARGO_BIN_EXE_verify"))
        .env("VENTICORN_LIBRARY", &directory.0)
        .args(["--module", &module])
        .output()
        .expect("run verify");

    assert_eq!(output.status.code(), Some(1));
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("is not loaded"), "{stdout}");
    assert!(stdout.contains("Build failed."), "{stdout}");
}

#[test]
fn verify_does_not_discard_match_statement_case_goals() {
    let directory = TestDirectory::new();
    directory.write(
        "main.ac",
        r#"
inductive Choice {
    first
    second
}
let choice: Choice = axiom
theorem apparent_success { true } by {
    match choice {
        Choice.first { false }
        Choice.second { true }
    }
}
"#,
    );
    let output = Command::new(env!("CARGO_BIN_EXE_verify"))
        .env("VENTICORN_LIBRARY", &directory.0)
        .args(["--module", "main"])
        .output()
        .expect("run verify on match statement");
    assert_eq!(output.status.code(), Some(1));
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stdout.contains("match statements are not supported yet"),
        "{stdout}\n{stderr}"
    );
    assert!(stdout.contains("Build failed."), "{stdout}");
    assert!(!stderr.contains("panicked"), "{stderr}");
}
