// Modified for Venticorn: reuse only completed proofs for the exact current module graph.
use std::path::PathBuf;
use venticorn::builder::{BuildCache, BuildEvent, BuildStatus, Builder};
use venticorn::module::ModuleRef;
use venticorn::project::Project;

fn run(project: &Project, old: BuildCache) -> (i32, i32, Vec<BuildEvent>, BuildCache) {
    let mut events = Vec::new();
    let (fresh, reused, cache) = {
        let mut builder = Builder::with_cache(old, |event| events.push(event));
        project.build(&mut builder);
        assert_eq!(builder.status, BuildStatus::Good);
        assert_eq!(builder.goals_done, builder.goals_total);
        (
            builder.num_success,
            builder.num_cached,
            builder.take_cache().unwrap(),
        )
    };
    (fresh, reused, events, cache)
}

fn graph() -> Project {
    let mut project = Project::new_mock();
    project.mock(
        "/mock/leaf.ac",
        "let value: Bool = true\ntheorem identity { value = value }",
    );
    project.mock(
        "/mock/middle.ac",
        "import leaf\nlet value: Bool = leaf.value\ntheorem identity { value = leaf.value }",
    );
    project.mock(
        "/mock/main.ac",
        "import middle\ntheorem outer { middle.value = middle.value } by {\n middle.value = middle.value\n}\n",
    );
    project
}

#[test]
fn unchanged_reuse_preserves_full_ranges_and_progress_order() {
    let project = graph();
    let (fresh, reused, original, cache) = run(&project, BuildCache::default());
    assert_eq!((fresh, reused), (4, 0));
    let (fresh, reused, replay, cache) = run(&project, cache);
    assert_eq!((fresh, reused), (0, 4));
    let observed = |events: Vec<BuildEvent>| {
        events
            .into_iter()
            .map(|e| {
                assert!(e.diagnostic.is_none());
                (e.module, e.verified, e.progress)
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(observed(original), observed(replay));
    assert_eq!(
        cache
            .get(&ModuleRef::Name("main".into()))
            .unwrap()
            .verified(),
        &[(2, 2), (1, 3)]
    );
    let (fresh, reused, _, _) = run(&project, cache);
    assert_eq!((fresh, reused), (0, 4));
}

#[test]
fn source_and_transitive_dependency_edits_invalidate_only_affected_modules() {
    let mut project = graph();
    let (_, _, _, cache) = run(&project, BuildCache::default());
    project
        .update_file(
            PathBuf::from("/mock/main.ac"),
            "import middle\ntheorem outer { middle.value = middle.value }",
            1,
        )
        .unwrap();
    let (fresh, reused, _, cache) = run(&project, cache);
    assert_eq!((fresh, reused), (1, 2));
    project
        .update_file(
            PathBuf::from("/mock/leaf.ac"),
            "let value: Bool = true\ntheorem identity { value = value }\n",
            1,
        )
        .unwrap();
    let (fresh, reused, _, _) = run(&project, cache);
    assert_eq!((fresh, reused), (3, 0));
}

#[test]
fn logical_identity_survives_changed_load_ids_and_unrelated_targets() {
    let project = graph();
    let (_, _, _, cache) = run(&project, BuildCache::default());
    let mut reordered = graph();
    reordered.mock("/mock/another.ac", "theorem identity { true }");
    assert_ne!(
        project
            .get_env_by_ref(&ModuleRef::Name("main".into()))
            .unwrap()
            .module_id,
        reordered
            .get_env_by_ref(&ModuleRef::Name("main".into()))
            .unwrap()
            .module_id
    );
    let (fresh, reused, _, _) = run(&reordered, cache);
    assert_eq!((fresh, reused), (1, 4));
}

#[test]
fn failed_dependency_prevents_reusing_a_locally_successful_importer() {
    let mut project = Project::new_mock();
    project.mock("/mock/failed.ac", "theorem impossible { false }");
    project.mock("/mock/main.ac", "import failed\ntheorem identity { true }");
    let mut first = Builder::new(|_| {});
    project.build(&mut first);
    assert_eq!(first.status, BuildStatus::Warning);
    let cache = first.take_cache().unwrap();
    assert!(cache.get(&ModuleRef::Name("failed".into())).is_none());
    assert!(cache.get(&ModuleRef::Name("main".into())).is_some());
    let mut second = Builder::with_cache(cache, |_| {});
    project.build(&mut second);
    assert_eq!(second.status, BuildStatus::Warning);
    assert_eq!(
        (second.num_success, second.num_cached, second.goals_done),
        (1, 0, 2)
    );
}

#[test]
fn changing_a_proved_goal_to_false_cannot_replay_its_old_success() {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", "theorem claim { true }");
    let (_, _, _, cache) = run(&project, BuildCache::default());
    project
        .update_file(PathBuf::from("/mock/main.ac"), "theorem claim { false }", 1)
        .unwrap();
    let mut events = Vec::new();
    {
        let mut builder = Builder::with_cache(cache, |event| events.push(event));
        project.build(&mut builder);
        assert_eq!(builder.status, BuildStatus::Warning);
        assert_eq!((builder.num_success, builder.num_cached), (0, 0));
        assert_eq!(builder.cache().unwrap().num_modules(), 0);
    }
    assert!(!events.iter().any(|e| e.verified.is_some()));
    assert!(events.iter().any(|e| e.diagnostic.is_some()));
}

#[test]
fn cancellation_during_replay_stops_further_verified_events_and_discards_new_cache() {
    let project = graph();
    let (_, _, _, cache) = run(&project, BuildCache::default());
    let mut count = 0;
    {
        let mut builder = Builder::with_cache(cache.clone(), |event| {
            if event.verified.is_some() {
                count += 1;
                project.stop_build();
            }
        });
        project.build(&mut builder);
        assert_eq!(builder.status, BuildStatus::Error);
        assert!(builder.cache().is_none());
        assert_eq!(builder.num_cached, 1);
    }
    assert_eq!(count, 1);
    let mut stopped = Builder::with_cache(cache, |event| assert!(event.verified.is_none()));
    project.build(&mut stopped);
    assert_eq!(stopped.status, BuildStatus::Error);
    assert_eq!((stopped.num_success, stopped.num_cached), (0, 0));
    assert!(stopped.cache().is_none());
}

#[test]
fn dataset_collection_performs_fresh_searches() {
    let project = graph();
    let (_, _, _, cache) = run(&project, BuildCache::default());
    let mut builder = Builder::with_cache(cache, |_| {});
    builder.create_dataset();
    project.build(&mut builder);
    assert_eq!(builder.status, BuildStatus::Good);
    assert_eq!((builder.num_success, builder.num_cached), (4, 0));
}

#[test]
fn empty_modules_retain_complete_cache_entries() {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", "");
    let (_, _, _, cache) = run(&project, BuildCache::default());
    let (fresh, reused, _, cache) = run(&project, cache);
    assert_eq!((fresh, reused, cache.num_modules()), (0, 0, 1));
}
