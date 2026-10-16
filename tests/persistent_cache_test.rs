use std::fs;
use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};
use venticorn::builder::{BuildStatus, Builder};
use venticorn::persistent_cache::CachePolicy;
use venticorn::project::Project;

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Library(PathBuf);
impl Library {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "venticorn_cache_read_{}_{}",
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
    fn cli(&self, args: &[&str]) -> Output {
        Command::new(env!("CARGO_BIN_EXE_verify"))
            .env("VENTICORN_LIBRARY", &self.0)
            .args(args)
            .output()
            .unwrap()
    }
}
impl Drop for Library {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn fresh_projects_reuse_only_validated_complete_goals_and_keep_real_prefixes() {
    let library = Library::new();
    library.write(
        "main.ac",
        "theorem first { true }\ntheorem second { true }\n",
    );
    assert_eq!(
        library
            .project(CachePolicy::ReadWrite)
            .sync_build_report()
            .num_success,
        2
    );
    let mut project = library.project(CachePolicy::ReadOnly);
    let warm = project.sync_build_report();
    assert_eq!(
        (warm.num_success, warm.num_cached, warm.goals_done),
        (0, 2, 2)
    );
    let original = warm.cache.unwrap();
    project
        .update_file(
            library.0.join("main.ac"),
            "theorem first { true }\ntheorem second { true }\ntheorem third { true }\n",
            1,
        )
        .unwrap();
    let mut builder = Builder::with_cache(original, |_| {});
    project.build(&mut builder);
    assert_eq!(builder.status, BuildStatus::Good);
    assert_eq!((builder.num_success, builder.num_cached), (1, 2));
}

#[test]
fn canonical_goals_survive_changed_load_ids_with_generic_data_and_phantom_actuals() {
    let library = Library::new();
    library.write("types.ac", "structure Box<T, U> {\n value: T\n}");
    library.write(
        "main.ac",
        "from types import Box\ntheorem identity<T, U>(x: Box<T, U>) { x.value = x.value }",
    );
    assert_eq!(
        library
            .project(CachePolicy::ReadWrite)
            .sync_build_report()
            .num_success,
        1
    );
    library.write("unrelated.ac", "theorem additional { true }");
    let mut project = Project::from_library_root(library.0.clone()).unwrap();
    project.set_cache_policy(CachePolicy::ReadOnly);
    project.load_module_by_name("unrelated").unwrap();
    project.add_all_targets().unwrap();
    let report = project.sync_build_report();
    assert_eq!(report.status, BuildStatus::Good);
    assert_eq!((report.num_success, report.num_cached), (1, 1));
}

#[test]
fn every_identity_field_and_malformed_or_oversized_records_are_cache_misses() {
    let library = Library::new();
    library.write("main.ac", "theorem okay { true }");
    library.project(CachePolicy::ReadWrite).sync_build_report();
    let path = library.records().pop().unwrap();
    let original = fs::read(&path).unwrap();
    for field in [
        "schema",
        "checker",
        "root",
        "module",
        "source",
        "dependencies",
        "goal_policy",
    ] {
        let mut value: serde_json::Value = serde_json::from_slice(&original).unwrap();
        match field {
            "schema" => value[field] = 99.into(),
            "checker" => value[field] = "another checker".into(),
            _ => value[field][0] = ((value[field][0].as_u64().unwrap() + 1) % 256).into(),
        }
        fs::write(&path, serde_json::to_vec(&value).unwrap()).unwrap();
        let report = library.project(CachePolicy::ReadOnly).sync_build_report();
        assert_eq!((report.num_success, report.num_cached), (1, 0), "{field}");
    }
    for bytes in [b"{".to_vec(), vec![b' '; 32 * 1024], b"null".to_vec()] {
        fs::write(&path, bytes).unwrap();
        let report = library.project(CachePolicy::ReadOnly).sync_build_report();
        assert_eq!((report.num_success, report.num_cached), (1, 0));
    }
}

#[test]
fn edited_sources_and_transitive_dependencies_cannot_reuse_old_success() {
    let library = Library::new();
    library.write("leaf.ac", "theorem leaf { true }");
    library.write("middle.ac", "import leaf\ntheorem middle { true }");
    library.write("main.ac", "import middle\ntheorem main { true }");
    library.project(CachePolicy::ReadWrite).sync_build_report();
    assert_eq!(
        library
            .project(CachePolicy::ReadOnly)
            .sync_build_report()
            .num_cached,
        3
    );
    library.write("leaf.ac", "theorem leaf { true }\n");
    let changed = library.project(CachePolicy::ReadOnly).sync_build_report();
    assert_eq!((changed.num_success, changed.num_cached), (3, 0));
    library.write("main.ac", "import middle\ntheorem main { false }");
    let false_claim = library.project(CachePolicy::ReadOnly).sync_build_report();
    assert_eq!(false_claim.status, BuildStatus::Warning);
    assert_eq!(false_claim.num_cached, 0);
}

#[test]
fn unsaved_snapshots_and_another_library_root_do_not_read_saved_successes() {
    let library = Library::new();
    library.write("main.ac", "theorem okay { true }");
    library.project(CachePolicy::ReadWrite).sync_build_report();
    let mut project = library.project(CachePolicy::ReadOnly);
    project
        .update_file(library.0.join("main.ac"), "theorem okay { true }\n", 1)
        .unwrap();
    let report = project.sync_build_report();
    assert_eq!((report.num_success, report.num_cached), (1, 0));
    let other = Library::new();
    other.write("main.ac", "theorem okay { true }");
    fs::create_dir(other.0.join(".venticorn-cache")).unwrap();
    for path in library.records() {
        fs::copy(
            &path,
            other
                .0
                .join(".venticorn-cache")
                .join(path.file_name().unwrap()),
        )
        .unwrap();
    }
    let report = other.project(CachePolicy::ReadOnly).sync_build_report();
    assert_eq!((report.num_success, report.num_cached), (1, 0));
}

#[test]
fn disabled_policy_bypasses_memory_even_with_an_explicit_prior_cache() {
    let library = Library::new();
    library.write("main.ac", "theorem okay { true }");
    let original = library
        .project(CachePolicy::ReadWrite)
        .sync_build_report()
        .cache
        .unwrap();
    let project = library.project(CachePolicy::Disabled);
    let mut builder = Builder::with_cache(original, |_| {});
    project.build(&mut builder);
    assert_eq!((builder.num_success, builder.num_cached), (1, 0));
    assert_eq!(project.cached_build().num_modules(), 0);
}

#[test]
fn cli_cold_warm_and_no_cache_runs_use_fresh_processes_and_preserve_false_controls() {
    let library = Library::new();
    library.write("main.ac", "theorem okay { true }");
    let default = library.cli(&[]);
    assert!(default.status.success());
    assert!(library.records().is_empty());
    let cold = library.cli(&["--cache"]);
    assert!(
        cold.status.success(),
        "{}",
        String::from_utf8_lossy(&cold.stderr)
    );
    let path = library.records().pop().unwrap();
    let original = fs::read(&path).unwrap();
    let modified = fs::metadata(&path).unwrap().modified().unwrap();
    let warm = library.cli(&["--cache"]);
    assert!(warm.status.success());
    let text = String::from_utf8_lossy(&warm.stdout);
    assert!(
        text.contains("1 goals reused from completed builds"),
        "{text}"
    );
    for args in [&[][..], &["--no-cache"][..]] {
        let cold = library.cli(args);
        assert!(cold.status.success());
        let text = String::from_utf8_lossy(&cold.stdout);
        assert!(
            text.contains("1/1 OK") && !text.contains("goals reused"),
            "{text}"
        );
    }
    assert_eq!(fs::read(&path).unwrap(), original);
    assert_eq!(fs::metadata(&path).unwrap().modified().unwrap(), modified);
    library.write("main.ac", "theorem okay { false }");
    for args in [&[][..], &["--cache"][..], &["--no-cache"][..]] {
        let false_claim = library.cli(args);
        assert_eq!(false_claim.status.code(), Some(1));
        assert!(String::from_utf8_lossy(&false_claim.stdout).contains("warnings"));
    }
    assert_eq!(fs::read(&path).unwrap(), original);
    let cold_library = Library::new();
    cold_library.write("main.ac", "theorem okay { true }");
    assert!(cold_library.cli(&["--no-cache"]).status.success());
    assert!(cold_library.records().is_empty());
    let conflicting = cold_library.cli(&["--cache", "--no-cache"]);
    assert_eq!(conflicting.status.code(), Some(2));
    assert!(cold_library.records().is_empty());
}

#[test]
fn nested_homonyms_reuse_independently_and_read_only_never_rewrites_records() {
    let library = Library::new();
    library.write("one/same.ac", "theorem okay { true }");
    library.write("two/same.ac", "theorem okay { true }");
    library.project(CachePolicy::ReadWrite).sync_build_report();
    let records = library.records();
    assert_eq!(records.len(), 2);
    let original = records
        .iter()
        .map(|path| fs::read(path).unwrap())
        .collect::<Vec<_>>();
    assert_eq!(
        library
            .project(CachePolicy::ReadOnly)
            .sync_build_report()
            .num_cached,
        2
    );
    library.write("one/same.ac", "theorem okay { true }\n");
    let report = library.project(CachePolicy::ReadOnly).sync_build_report();
    assert_eq!((report.num_success, report.num_cached), (1, 1));
    assert_eq!(
        records
            .iter()
            .map(|path| fs::read(path).unwrap())
            .collect::<Vec<_>>(),
        original
    );
}

#[cfg(unix)]
#[test]
fn a_symlinked_record_is_a_miss_even_when_its_content_matches() {
    let library = Library::new();
    library.write("main.ac", "theorem okay { true }");
    library.project(CachePolicy::ReadWrite).sync_build_report();
    let path = library.records().pop().unwrap();
    let other = library.0.join("borrowed.json");
    fs::rename(&path, &other).unwrap();
    std::os::unix::fs::symlink(&other, &path).unwrap();
    let report = library.project(CachePolicy::ReadOnly).sync_build_report();
    assert_eq!((report.num_success, report.num_cached), (1, 0));
}

#[cfg(unix)]
#[test]
fn unsaved_alias_excludes_saved_named_sources_and_transitive_importers() {
    let library = Library::new();
    library.write("leaf.ac", "theorem leaf { true }");
    library.write("main.ac", "import leaf\ntheorem main { true }");
    assert_eq!(
        library
            .project(CachePolicy::ReadWrite)
            .sync_build_report()
            .num_success,
        2
    );
    let alias_root = Library::new();
    let alias = alias_root.0.join("leaf.ac");
    std::os::unix::fs::symlink(library.0.join("leaf.ac"), &alias).unwrap();
    for changed in [true, false] {
        let mut project = library.project(CachePolicy::ReadOnly);
        project
            .update_file(
                alias.clone(),
                if changed {
                    "theorem leaf { true }\n"
                } else {
                    "theorem leaf { true }"
                },
                1,
            )
            .unwrap();
        let report = project.sync_build_report();
        assert_eq!(report.status, BuildStatus::Good);
        assert_eq!(report.num_cached, if changed { 0 } else { 2 });
    }
}

#[test]
fn filtered_cli_reproves_each_goal_and_rejects_conflicting_cache_modes() {
    let library = Library::new();
    let facts = "let seed: Bool = axiom\nlet flag: Bool = axiom\naxiom start { seed }\naxiom known { seed implies flag }\n";
    let source = format!("{facts}theorem first {{ flag }}\ntheorem second {{ flag and seed }}");
    library.write("main.ac", &source);
    assert!(library.cli(&["--cache"]).status.success());
    for mode in ["--filtered", "--cache"] {
        let result = library.cli(&[mode]);
        assert!(result.status.success(), "{result:?}");
        let output = String::from_utf8(result.stdout).unwrap();
        #[cfg(feature = "onnx")]
        assert!(
            !output.contains("Could not load the proof-scoring model")
                && !String::from_utf8_lossy(&result.stderr)
                    .contains("Could not load the proof-scoring model")
        );
        if mode == "--filtered" {
            assert!(
                output.contains("2 searches performed") && !output.contains("goals reused"),
                "{output}"
            );
        } else {
            assert!(
                output.contains("0 searches performed") && output.contains("2 goals reused"),
                "{output}"
            );
        }
    }
    for conflict in ["--cache", "--no-cache"] {
        assert_eq!(
            library.cli(&["--filtered", conflict]).status.code(),
            Some(2)
        );
    }
    let mut project = library.project(CachePolicy::ReadOnly);
    project.check_hashes = false;
    let mut builder = project.builder(|_| {});
    project.build(&mut builder);
    assert_eq!(builder.status, BuildStatus::Good);
    assert_eq!(
        (
            builder.searches_total,
            builder.hinted_searches,
            builder.num_cached
        ),
        (2, 2, 0)
    );
    let mut dataset = project.builder(|_| {});
    dataset.create_dataset();
    project.build(&mut dataset);
    assert_eq!(dataset.status, BuildStatus::Good);
    assert_eq!(
        (
            dataset.searches_total,
            dataset.hinted_searches,
            dataset.num_cached
        ),
        (2, 0, 0)
    );
    // A matching first block must not be reused when the later claim changes.
    library.write("main.ac", &source.replace("flag and seed", "not flag"));
    let false_claim = library.cli(&["--filtered"]);
    assert_eq!(false_claim.status.code(), Some(1));
    let output = String::from_utf8(false_claim.stdout).unwrap();
    assert!(
        output.contains("1/2 OK") && !output.contains("goals reused"),
        "{output}"
    );
}
