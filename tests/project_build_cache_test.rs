// Modified for Venticorn: shared cache publication is atomic and preserves prior valid entries.
use std::path::PathBuf;
use venticorn::builder::{BuildStatus, Builder};
use venticorn::module::ModuleRef;
use venticorn::project::Project;

fn named(name: &str) -> ModuleRef {
    ModuleRef::Name(name.into())
}

#[test]
fn repeated_builds_reuse_then_reverify_source_and_dependency_edits() {
    let mut project = Project::new_mock();
    let dependency = "type Item: axiom\nlet a: Item = axiom\nlet b: Item = axiom\nlet c: Item = axiom\naxiom ab { a = b }\naxiom bc { b = c }\ntheorem ac { a = c }";
    let main = "import dependency\ntheorem equality { dependency.a = dependency.c }";
    project.mock("/mock/dependency.ac", dependency);
    project.mock("/mock/main.ac", main);
    let first = project.sync_build_report();
    assert_eq!(first.status, BuildStatus::Good);
    assert_eq!((first.num_success, first.num_cached), (2, 0));
    let again = project.sync_build_report();
    assert_eq!(again.status, BuildStatus::Good);
    assert_eq!(
        (
            again.num_success,
            again.num_cached,
            again.goals_done,
            again.goals_total
        ),
        (0, 2, 2, 2)
    );
    project
        .update_file(PathBuf::from("/mock/main.ac"), &format!("{main}\n"), 1)
        .unwrap();
    let changed = project.sync_build_report();
    assert_eq!(changed.status, BuildStatus::Good);
    assert_eq!((changed.num_success, changed.num_cached), (1, 1));
    project
        .update_file(
            PathBuf::from("/mock/dependency.ac"),
            &format!("{dependency}\n"),
            1,
        )
        .unwrap();
    let changed = project.sync_build_report();
    assert_eq!(changed.status, BuildStatus::Good);
    assert_eq!((changed.num_success, changed.num_cached), (2, 0));
}

#[test]
fn callbacks_see_only_prior_completed_entries_and_cancel_does_not_publish_partial_work() {
    let mut project = Project::new_mock();
    project.mock("/mock/old.ac", "theorem old { true }");
    assert_eq!(project.sync_build_report().num_success, 1);
    project.mock("/mock/anew.ac", "theorem new { true }");
    project.mock("/mock/zlast.ac", "theorem last { true }");
    let mut builder = Builder::with_cache(project.cached_build(), |event| {
        // A callback may safely inspect the shared cache; no cache lock is held while emitting.
        assert_eq!(project.cached_build().num_modules(), 1);
        assert!(project.cached_build().get(&named("anew")).is_none());
        if event.verified.is_some() {
            project.stop_build();
        }
    });
    project.build(&mut builder);
    assert_eq!(builder.status, BuildStatus::Error);
    assert!(builder.cache().is_none());
    assert_eq!(project.cached_build().num_modules(), 1);
    assert!(project.cached_build().get(&named("old")).is_some());
    drop(builder);
    project.allow_build();
    let completed = project.sync_build_report();
    assert_eq!(completed.status, BuildStatus::Good);
    assert_eq!((completed.num_success, completed.num_cached), (2, 1));
    assert_eq!(project.cached_build().num_modules(), 3);
}

#[test]
fn failed_load_preserves_previous_cache_but_cannot_reuse_changed_false_goals() {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", "theorem claim { true }");
    assert_eq!(project.sync_build_report().num_success, 1);
    let original = project
        .cached_build()
        .get(&named("main"))
        .unwrap()
        .fingerprint();
    project
        .update_file(PathBuf::from("/mock/main.ac"), "theorem claim {", 1)
        .unwrap();
    let failed = project.sync_build_report();
    assert_eq!(failed.status, BuildStatus::Error);
    assert!(failed.cache.is_none());
    assert_eq!(
        project
            .cached_build()
            .get(&named("main"))
            .unwrap()
            .fingerprint(),
        original
    );
    project
        .update_file(PathBuf::from("/mock/main.ac"), "theorem claim { false }", 2)
        .unwrap();
    for _ in 0..2 {
        let failed = project.sync_build_report();
        assert_eq!(failed.status, BuildStatus::Warning);
        assert_eq!((failed.num_success, failed.num_cached), (0, 0));
        assert!(!failed.events.iter().any(|event| event.verified.is_some()));
    }
    project
        .update_file(PathBuf::from("/mock/main.ac"), "theorem claim { true }", 3)
        .unwrap();
    let restored = project.sync_build_report();
    assert_eq!(restored.status, BuildStatus::Good);
    assert_eq!((restored.num_success, restored.num_cached), (0, 1));
}

#[test]
fn warnings_publish_only_independent_successful_modules() {
    let mut project = Project::new_mock();
    project.mock("/mock/good.ac", "theorem good { true }");
    project.mock("/mock/bad.ac", "theorem bad { false }");
    let first = project.sync_build_report();
    assert_eq!(first.status, BuildStatus::Warning);
    assert_eq!((first.num_success, first.num_cached), (1, 0));
    assert_eq!(project.cached_build().num_modules(), 1);
    let second = project.sync_build_report();
    assert_eq!(second.status, BuildStatus::Warning);
    assert_eq!((second.num_success, second.num_cached), (0, 1));
    assert!(second
        .events
        .iter()
        .any(|event| event.module == named("bad") && event.diagnostic.is_some()));
}
