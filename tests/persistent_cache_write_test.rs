use std::fs;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use venticorn::builder::BuildStatus;
use venticorn::persistent_cache::{checker_identity, CachePolicy};
use venticorn::project::Project;

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Library(PathBuf);
impl Library {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "venticorn_cache_write_{}_{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path.canonicalize().unwrap())
    }
    fn write(&self, name: &str, text: &str) {
        let path = self.0.join(name);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, text).unwrap();
    }
    fn project(&self, policy: CachePolicy) -> Project {
        let mut project = Project::from_library_root(self.0.clone()).unwrap();
        project.set_cache_policy(policy);
        project.add_all_targets().unwrap();
        project
    }
    fn records(&self) -> Vec<PathBuf> {
        let mut files = fs::read_dir(self.0.join(".venticorn-cache"))
            .into_iter()
            .flatten()
            .map(|entry| entry.unwrap().path())
            .collect::<Vec<_>>();
        files.sort();
        files
    }
}
impl Drop for Library {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn finalized_successes_write_atomic_named_records_and_unchanged_builds_do_not_rewrite() {
    let library = Library::new();
    library.write("one/same.ac", "theorem first { true }");
    library.write("two/same.ac", "theorem second { true }");
    let project = library.project(CachePolicy::ReadWrite);
    let report = project.sync_build_report();
    assert_eq!(report.status, BuildStatus::Good);
    assert_eq!(report.num_success, 2);
    let records = library.records();
    assert_eq!(records.len(), 2);
    let before = records
        .iter()
        .map(|path| {
            (
                fs::read(path).unwrap(),
                fs::metadata(path).unwrap().modified().unwrap(),
            )
        })
        .collect::<Vec<_>>();
    for path in &records {
        assert_eq!(path.extension().unwrap(), "json");
        let record: serde_json::Value = serde_json::from_slice(&fs::read(path).unwrap()).unwrap();
        assert_eq!(record["schema"], 2);
        assert!(record["hints"].is_object());
        assert_eq!(record["checker"], checker_identity());
        assert_eq!(record["goal_policy"].as_array().unwrap().len(), 32);
    }
    assert_ne!(before[0].0, before[1].0);
    let report = project.sync_build_report();
    assert_eq!((report.num_success, report.num_cached), (0, 2));
    let after = records
        .iter()
        .map(|path| {
            (
                fs::read(path).unwrap(),
                fs::metadata(path).unwrap().modified().unwrap(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(before, after);
}

#[test]
fn memory_read_only_and_disabled_policies_do_not_create_disk_records() {
    for policy in [
        CachePolicy::MemoryOnly,
        CachePolicy::ReadOnly,
        CachePolicy::Disabled,
    ] {
        let library = Library::new();
        library.write("main.ac", "theorem okay { true }");
        let project = library.project(policy);
        assert_eq!(project.sync_build_report().num_success, 1);
        let second = project.sync_build_report();
        assert_eq!(
            second.num_cached,
            if policy == CachePolicy::Disabled {
                0
            } else {
                1
            }
        );
        assert!(!library.0.join(".venticorn-cache").exists());
    }
}

#[test]
fn warning_error_and_interrupted_builds_do_not_publish_partial_successes() {
    for invalid in ["theorem false_goal { false }", "theorem unfinished {"] {
        let library = Library::new();
        library.write("good.ac", "theorem okay { true }");
        library.write("bad.ac", invalid);
        assert_ne!(
            library
                .project(CachePolicy::ReadWrite)
                .sync_build_report()
                .status,
            BuildStatus::Good
        );
        assert!(library.records().is_empty());
    }
    let library = Library::new();
    library.write("main.ac", "theorem one { true }\ntheorem two { true }");
    let project = library.project(CachePolicy::ReadWrite);
    let mut builder = project.builder(|event| {
        if event.verified.is_some() {
            project.stop_build();
        }
    });
    project.build(&mut builder);
    assert!(builder.cache().is_none());
    assert!(library.records().is_empty());
}

#[test]
fn unsaved_source_or_transitive_dependencies_never_become_saved_successes() {
    for changed in ["leaf.ac", "main.ac"] {
        let library = Library::new();
        library.write("leaf.ac", "theorem leaf { true }");
        library.write("middle.ac", "import leaf\ntheorem middle { true }");
        library.write("main.ac", "import middle\ntheorem main { true }");
        let mut project = library.project(CachePolicy::ReadWrite);
        let path = library.0.join(changed);
        let text = fs::read_to_string(&path).unwrap() + "\n";
        project.update_file(path, &text, 1).unwrap();
        assert_eq!(project.sync_build_report().status, BuildStatus::Good);
        assert_eq!(
            library.records().len(),
            if changed == "leaf.ac" { 0 } else { 2 }
        );
    }
    let library = Library::new();
    library.write("main.ac", "theorem okay { true }");
    let project = library.project(CachePolicy::ReadWrite);
    library.write("main.ac", "theorem changed { false }");
    assert_eq!(project.sync_build_report().status, BuildStatus::Good);
    assert!(library.records().is_empty());
}

#[test]
fn cache_io_failure_does_not_change_verification_status() {
    let library = Library::new();
    library.write("main.ac", "theorem okay { true }");
    library.write(".venticorn-cache", "not a directory");
    assert_eq!(
        library
            .project(CachePolicy::ReadWrite)
            .sync_build_report()
            .status,
        BuildStatus::Good
    );
    assert_eq!(
        fs::read_to_string(library.0.join(".venticorn-cache")).unwrap(),
        "not a directory"
    );
}

#[cfg(unix)]
#[test]
fn a_symlinked_cache_directory_is_not_written() {
    let library = Library::new();
    let destination = Library::new();
    library.write("main.ac", "theorem okay { true }");
    std::os::unix::fs::symlink(&destination.0, library.0.join(".venticorn-cache")).unwrap();
    assert_eq!(
        library
            .project(CachePolicy::ReadWrite)
            .sync_build_report()
            .status,
        BuildStatus::Good
    );
    assert_eq!(fs::read_dir(&destination.0).unwrap().count(), 0);
}

#[cfg(unix)]
#[test]
fn unsaved_symlink_overlay_excludes_the_named_module_and_its_importers() {
    let library = Library::new();
    library.write("leaf.ac", "theorem leaf { true }");
    library.write("main.ac", "import leaf\ntheorem main { true }");
    let alias_root = Library::new();
    let alias = alias_root.0.join("leaf.ac");
    std::os::unix::fs::symlink(library.0.join("leaf.ac"), &alias).unwrap();
    let mut project = library.project(CachePolicy::ReadWrite);
    project
        .update_file(alias.clone(), "theorem leaf { true }\n", 1)
        .unwrap();
    assert_eq!(project.sync_build_report().status, BuildStatus::Good);
    assert!(library.records().is_empty());
    project
        .update_file(alias, "theorem leaf { true }", 2)
        .unwrap();
    assert_eq!(project.sync_build_report().status, BuildStatus::Good);
    assert_eq!(library.records().len(), 3);
}
