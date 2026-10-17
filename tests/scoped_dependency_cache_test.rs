use std::collections::BTreeMap;
use std::fs;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use venticorn::builder::BuildStatus;
use venticorn::module::ModuleRef;
use venticorn::persistent_cache::CachePolicy;
use venticorn::project::Project;

static NEXT: AtomicU64 = AtomicU64::new(0);
const LEAF: &str = "axiom available { true }\n";
const MIDDLE: &str = "theorem middle { true } by {\n    import leaf\n}\n";
const MAIN: &str = "theorem outer { true } by {\n    theorem inner { true } by {\n        import middle\n    }\n}\n";

struct Library(PathBuf);
impl Library {
    fn new() -> Self {
        let root = std::env::temp_dir().join(format!(
            "venticorn_scoped_dependencies_{}_{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&root).unwrap();
        let library = Self(root.canonicalize().unwrap());
        library.write("leaf.ac", LEAF);
        library.write("middle.ac", MIDDLE);
        library.write("main.ac", MAIN);
        library
    }
    fn write(&self, name: &str, text: &str) {
        fs::write(self.0.join(name), text).unwrap();
    }
    fn project(&self, policy: CachePolicy) -> Project {
        let mut project = Project::from_library_root(self.0.clone()).unwrap();
        project.set_cache_policy(policy);
        project.add_all_targets().unwrap();
        project
    }
    fn records(&self) -> BTreeMap<PathBuf, Vec<u8>> {
        fs::read_dir(self.0.join(".venticorn-cache"))
            .unwrap()
            .map(|entry| {
                let path = entry.unwrap().path();
                let bytes = fs::read(&path).unwrap();
                (path, bytes)
            })
            .collect()
    }
}
impl Drop for Library {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn nested_proof_imports_affect_identity_and_cache_without_becoming_global_facts() {
    let library = Library::new();
    let project = library.project(CachePolicy::ReadWrite);
    let main = ModuleRef::Name("main".into());
    let middle = ModuleRef::Name("middle".into());
    let leaf = ModuleRef::Name("leaf".into());
    let main_env = project.get_env_by_ref(&main).unwrap();
    let main_id = main_env.module_id;
    let before = project.get_module_hash(main_id).unwrap().clone();
    assert!(main_env.bindings.direct_dependencies().is_empty());
    assert!(project.all_dependencies(main_id).is_empty());
    assert!(project.imported_facts(main_id).is_empty());
    let cold = project.sync_build_report();
    assert_eq!(cold.status, BuildStatus::Good);
    assert_eq!((cold.num_success, cold.num_cached), (3, 0));
    let cache = cold.cache.unwrap();
    assert_eq!(
        cache.get(&main).unwrap().direct_dependencies(),
        &[middle.clone()]
    );
    assert_eq!(cache.get(&middle).unwrap().direct_dependencies(), &[leaf]);

    let warm = library.project(CachePolicy::ReadOnly).sync_build_report();
    assert_eq!(warm.status, BuildStatus::Good);
    assert_eq!((warm.num_success, warm.num_cached), (0, 3));

    // Neither importer changed; the leaf is reached only through nested proof imports.
    library.write("leaf.ac", &format!("{LEAF}// edited dependency\n"));
    let changed = library.project(CachePolicy::ReadOnly);
    let changed_main = changed.get_env_by_ref(&main).unwrap().module_id;
    let after = changed.get_module_hash(changed_main).unwrap();
    assert_ne!(&before, after);
    assert_ne!(
        before.dependency_fingerprint(),
        after.dependency_fingerprint()
    );
    let report = changed.sync_build_report();
    assert_eq!(report.status, BuildStatus::Good);
    assert_eq!((report.num_success, report.num_cached), (3, 0));
}

#[test]
fn changed_disk_snapshot_excludes_nested_importers_from_reads_and_publication() {
    let library = Library::new();
    let initial = library.project(CachePolicy::ReadWrite).sync_build_report();
    assert_eq!(initial.status, BuildStatus::Good);
    let saved = library.records();
    assert_eq!(saved.len(), 3);

    // Load first, then change disk. The parsed snapshot is valid but no longer saved.
    let stale = library.project(CachePolicy::ReadWrite);
    library.write("leaf.ac", &format!("{LEAF}// newer saved bytes\n"));
    assert_eq!(stale.cached_build().num_modules(), 0);
    let result = stale.sync_build_report();
    assert_eq!(result.status, BuildStatus::Good);
    assert_eq!((result.num_success, result.num_cached), (3, 0));
    assert_eq!(library.records(), saved);

    // Reloading the current bytes permits new complete records and later warm reuse.
    let current = library.project(CachePolicy::ReadWrite).sync_build_report();
    assert_eq!(current.status, BuildStatus::Good);
    assert_eq!((current.num_success, current.num_cached), (3, 0));
    assert_ne!(library.records(), saved);
    let warm = library.project(CachePolicy::ReadOnly).sync_build_report();
    assert_eq!(
        (warm.status, warm.num_success, warm.num_cached),
        (BuildStatus::Good, 0, 3)
    );
}

#[test]
fn failed_requested_scoped_dependency_blocks_reuse_and_disk_publication() {
    let library = Library::new();
    let initial = library.project(CachePolicy::ReadWrite).sync_build_report();
    assert_eq!(initial.status, BuildStatus::Good);
    let saved = library.records();
    library.write("leaf.ac", "theorem invalid { false }\n");
    let project = library.project(CachePolicy::ReadWrite);
    for _ in 0..2 {
        let report = project.sync_build_report();
        assert_eq!(report.status, BuildStatus::Warning);
        assert_eq!((report.num_success, report.num_cached), (3, 0));
        // Successful local importer goals do not make a failed dependency trusted.
        assert_eq!(library.records(), saved);
    }
}
