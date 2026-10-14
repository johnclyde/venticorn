// Modified for Venticorn: exercise file and module selection through the verifier.
use std::fs;
use std::path::PathBuf;
use std::process::{Command, Output};

struct Fixture(PathBuf);
impl Fixture {
    fn new(name: &str) -> Self {
        let root =
            std::env::temp_dir().join(format!("venticorn_target_{}_{name}", std::process::id()));
        fs::create_dir_all(root.join("library")).unwrap();
        fs::write(
            root.join("library/base.ac"),
            "type Item: axiom\nlet item: Item = axiom",
        )
        .unwrap();
        fs::write(
            root.join("library/main.ac"),
            "import base\ntheorem identity { base.item = base.item }",
        )
        .unwrap();
        fs::write(
            root.join("library/broken.ac"),
            "theorem impossible { false }",
        )
        .unwrap();
        fs::write(
            root.join("outside.ac"),
            "import base\ntheorem identity { base.item = base.item }",
        )
        .unwrap();
        Self(root)
    }
    fn run(&self, args: &[&str]) -> Output {
        Command::new(env!("CARGO_BIN_EXE_verify"))
            .current_dir(&self.0)
            .env("VENTICORN_LIBRARY", self.0.join("library"))
            .args(args)
            .output()
            .unwrap()
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
fn text(output: &Output) -> String {
    format!(
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    )
}
#[test]
fn file_and_module_targets_verify_only_the_selected_module() {
    let fixture = Fixture::new("success");
    let absolute = fixture.0.join("library/main.ac");
    for args in [
        vec!["main"],
        vec!["--module", "main"],
        vec!["library/../library/main.ac"],
        vec![absolute.to_str().unwrap()],
        vec!["outside.ac"],
    ] {
        let output = fixture.run(&args);
        assert!(output.status.success(), "{}", text(&output));
        assert!(text(&output).contains("1/1 OK"), "{}", text(&output));
    }
    let mut project =
        venticorn::project::Project::from_library_root(fixture.0.join("library")).unwrap();
    project
        .add_target_by_path(&fixture.0.join("library/../library/main.ac"))
        .unwrap();
    assert!(project
        .get_env_by_ref(&venticorn::module::ModuleRef::Name("main".to_string()))
        .is_some());
    assert!(project
        .get_env_by_ref(&venticorn::module::ModuleRef::File(absolute))
        .is_none());
}
#[test]
fn invalid_targets_and_failed_proofs_exit_unsuccessfully() {
    let fixture = Fixture::new("failure");
    fs::create_dir(fixture.0.join("directory.ac")).unwrap();
    fs::write(fixture.0.join("invalid.ac"), "theorem unfinished {").unwrap();
    for args in [
        vec!["missing.ac"],
        vec!["directory.ac"],
        vec!["missing"],
        vec!["../escape"],
        vec!["invalid.ac"],
        vec!["library/broken.ac"],
    ] {
        let output = fixture.run(&args);
        assert_eq!(output.status.code(), Some(1), "{}", text(&output));
        assert!(!text(&output).contains("panicked"), "{}", text(&output));
        assert!(
            text(&output).contains("error") || text(&output).contains("could not be verified"),
            "{}",
            text(&output)
        );
    }
    assert_eq!(
        fixture.run(&["main", "--module", "main"]).status.code(),
        Some(2)
    );
}
#[cfg(unix)]
#[test]
fn symlink_targets_keep_the_canonical_library_module_identity() {
    let fixture = Fixture::new("symlink");
    std::os::unix::fs::symlink(fixture.0.join("library/main.ac"), fixture.0.join("link.ac"))
        .unwrap();
    let mut project =
        venticorn::project::Project::from_library_root(fixture.0.join("library")).unwrap();
    project
        .add_target_by_path(&fixture.0.join("link.ac"))
        .unwrap();
    assert!(project
        .get_env_by_ref(&venticorn::module::ModuleRef::Name("main".to_string()))
        .is_some());
    assert!(fixture.run(&["link.ac"]).status.success());
}
