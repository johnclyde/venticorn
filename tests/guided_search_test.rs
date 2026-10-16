use std::path::PathBuf;
use venticorn::builder::{BuildCache, BuildEvent, BuildStatus, Builder};
use venticorn::module::ModuleRef;
use venticorn::persistent_cache::CachePolicy;
use venticorn::project::Project;

const FACTS: &str = "let seed: Bool = axiom\nlet first: Bool = axiom\nlet second: Bool = axiom\naxiom start { seed }\naxiom left { seed implies first }\naxiom right { seed implies second }\n";
fn main_ref() -> ModuleRef {
    ModuleRef::Name("main".into())
}
fn edit(project: &mut Project, source: &str, version: i32) {
    project
        .update_file(PathBuf::from("/mock/main.ac"), source, version)
        .unwrap();
    project
        .get_env_by_ref(&main_ref())
        .expect("current source admitted");
}
struct Run {
    status: BuildStatus,
    // searches, hinted attempts, accepted hints, fallbacks, fresh, reused, done
    counts: (i32, i32, i32, i32, i32, i32, i32),
    events: Vec<BuildEvent>,
    cache: Option<BuildCache>,
}
fn run(project: &Project, dataset: bool) -> Run {
    let mut events = vec![];
    let (status, counts, cache) = {
        let mut builder = project.builder(|event| events.push(event));
        if dataset {
            builder.create_dataset();
        }
        project.build(&mut builder);
        println!("guided metrics: searches={} hinted={} accepted={} fallbacks={} activations={} goals={}", builder.searches_total, builder.hinted_searches, builder.hinted_successes, builder.hint_fallbacks, builder.num_activated, builder.goals_done);
        (
            builder.status,
            (
                builder.searches_total,
                builder.hinted_searches,
                builder.hinted_successes,
                builder.hint_fallbacks,
                builder.num_success,
                builder.num_cached,
                builder.goals_done,
            ),
            builder.take_cache(),
        )
    };
    Run {
        status,
        counts,
        events,
        cache,
    }
}
fn good(run: &Run, goals: usize) {
    assert_eq!(run.status, BuildStatus::Good);
    assert_eq!(
        run.events.iter().filter(|e| e.verified.is_some()).count(),
        goals
    );
    assert!(run.events.iter().all(|e| e.diagnostic.is_none()));
}
fn learned() -> Project {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", &format!("{FACTS}theorem goal {{ first }}"));
    let cold = run(&project, false);
    good(&cold, 1);
    assert_eq!(cold.counts, (1, 0, 0, 0, 1, 0, 1));
    project
}

#[test]
fn edited_theorem_tries_advisory_premises_and_reports_one_goal() {
    let mut project = learned();
    edit(
        &mut project,
        &format!("{FACTS}theorem goal {{ first and first }}"),
        1,
    );
    let hit = run(&project, false);
    good(&hit, 1);
    assert_eq!(hit.counts, (1, 1, 1, 0, 1, 0, 1));
    // The old subset has no right axiom. Full search is independently available.
    edit(
        &mut project,
        &format!("{FACTS}theorem goal {{ second }}"),
        2,
    );
    let fallback = run(&project, false);
    good(&fallback, 1);
    assert_eq!(fallback.counts, (2, 1, 0, 1, 1, 0, 1));
    let cache = fallback.cache.unwrap();
    let names = &cache.get(&main_ref()).unwrap().theorem_premises()["goal"][&main_ref()];
    assert!(names.contains("right") && !names.contains("left"));
}

#[test]
fn stale_hints_cannot_verify_a_false_changed_claim() {
    let mut project = learned();
    edit(
        &mut project,
        &format!("{FACTS}theorem goal {{ not first }}"),
        1,
    );
    let result = run(&project, false);
    assert_eq!(result.status, BuildStatus::Warning);
    assert_eq!(result.counts, (2, 1, 0, 1, 0, 0, 1));
    assert_eq!(
        result
            .events
            .iter()
            .filter(|e| e.verified.is_some())
            .count(),
        0
    );
    assert_eq!(
        result
            .events
            .iter()
            .filter(|e| e.diagnostic.is_some())
            .count(),
        1
    );
    assert!(result.cache.unwrap().get(&main_ref()).is_none());
}

#[test]
fn nested_body_sources_remain_usable_without_early_admission() {
    let mut project = Project::new_mock();
    let facts = "let seed: Bool = axiom\nlet first: Bool = axiom\nlet second: Bool = axiom\naxiom start { seed }\naxiom left { seed implies first }\naxiom right { seed implies second }\n";
    project.mock(
        "/mock/main.ac",
        &format!("{facts}theorem goal {{ first and seed }} by {{\n first\n}}"),
    );
    let cold = run(&project, false);
    good(&cold, 2);
    let cache = cold.cache.unwrap();
    let names = &cache.get(&main_ref()).unwrap().theorem_premises()["goal"][&main_ref()];
    assert!(
        names.contains("8"),
        "expected actual body source: {names:?}"
    );
    edit(
        &mut project,
        &format!("{facts}theorem goal {{ second and seed }} by {{\n second\n}}"),
        1,
    );
    let result = run(&project, false);
    good(&result, 2);
    // Child falls back; parent uses the already proved body fact in the subset.
    assert_eq!(result.counts, (3, 2, 1, 1, 2, 0, 2));
}

#[test]
fn dataset_and_disabled_builds_bypass_hints_but_matching_memory_hints_survive_dataset() {
    let mut project = learned();
    let dataset = run(&project, true);
    good(&dataset, 1);
    assert_eq!(dataset.counts, (1, 0, 0, 0, 1, 0, 1));
    assert!(dataset
        .cache
        .unwrap()
        .get(&main_ref())
        .unwrap()
        .theorem_premises()
        .is_empty());
    let reused = run(&project, false);
    good(&reused, 1);
    assert_eq!(reused.counts, (0, 0, 0, 0, 0, 1, 1));
    assert!(reused
        .cache
        .unwrap()
        .get(&main_ref())
        .unwrap()
        .theorem_premises()
        .contains_key("goal"));
    edit(
        &mut project,
        &format!("{FACTS}theorem goal {{ first and first }}"),
        1,
    );
    assert_eq!(run(&project, false).counts, (1, 1, 1, 0, 1, 0, 1));
    edit(
        &mut project,
        &format!("{FACTS}theorem goal {{ second }}"),
        2,
    );
    good(&run(&project, true), 1);
    // A changed dataset snapshot must not resurrect the old theorem's hints.
    assert!(project
        .cached_build()
        .get(&main_ref())
        .unwrap()
        .theorem_premises()
        .is_empty());
    edit(
        &mut project,
        &format!("{FACTS}theorem goal {{ second and second }}"),
        3,
    );
    assert_eq!(run(&project, false).counts, (1, 0, 0, 0, 1, 0, 1));
    project.set_cache_policy(CachePolicy::Disabled);
    let disabled = run(&project, false);
    good(&disabled, 1);
    assert_eq!(disabled.counts, (1, 0, 0, 0, 1, 0, 1));
    assert!(disabled
        .cache
        .unwrap()
        .get(&main_ref())
        .unwrap()
        .theorem_premises()
        .is_empty());
}

#[test]
fn known_full_context_errors_and_inconsistency_are_not_hidden_by_a_subset() {
    for (extra, expected) in [
        ("axiom impossible { false }\n", BuildStatus::Warning),
        (
            "let unused: Bool = axiom\naxiom yes { unused }\naxiom no { not unused }\n",
            BuildStatus::Warning,
        ),
        ("axiom unsupported { f(false) }\n", BuildStatus::Error),
    ] {
        let mut project = Project::new_mock();
        let facts = format!("{FACTS}let f: Bool -> Bool = axiom\n");
        project.mock("/mock/main.ac", &format!("{facts}theorem goal {{ first }}"));
        good(&run(&project, false), 1);
        edit(
            &mut project,
            &format!("{facts}{extra}theorem goal {{ first }}"),
            1,
        );
        let result = run(&project, false);
        assert_eq!(result.status, expected, "{extra}");
        assert_eq!(result.counts, (1, 0, 0, 0, 0, 0, 1));
        assert!(result.events.iter().all(|e| e.verified.is_none()));
        if let Some(cache) = result.cache {
            assert!(cache.get(&main_ref()).is_none());
        }
    }
}

#[test]
fn standalone_files_use_canonical_premises_after_edits() {
    let mut project = Project::new_mock();
    let path = PathBuf::from("/outside/standalone.ac");
    project.mock(
        path.to_str().unwrap(),
        &format!("{FACTS}theorem goal {{ first }}"),
    );
    good(&run(&project, false), 1);
    project
        .update_file(
            path,
            &format!("{FACTS}theorem goal {{ first and first }}"),
            1,
        )
        .unwrap();
    let result = run(&project, false);
    good(&result, 1);
    assert_eq!(result.counts, (1, 1, 1, 0, 1, 0, 1));
}

#[test]
fn missing_retained_source_uses_one_ordinary_search() {
    let mut project = learned();
    let changed = FACTS.replace("axiom left", "axiom renamed");
    edit(
        &mut project,
        &format!("{changed}theorem goal {{ first }}"),
        1,
    );
    let result = run(&project, false);
    good(&result, 1);
    assert_eq!(result.counts, (1, 0, 0, 0, 1, 0, 1));
}

#[test]
fn cancellation_after_a_guided_child_stops_before_its_parent() {
    let mut project = Project::new_mock();
    project.mock(
        "/mock/main.ac",
        &format!("{FACTS}theorem goal {{ first and seed }} by {{\n first\n}}"),
    );
    good(&run(&project, false), 2);
    edit(
        &mut project,
        &format!("{FACTS}theorem goal {{ second and seed }} by {{\n second\n}}"),
        1,
    );
    let mut events = vec![];
    {
        let mut builder = Builder::with_cache(project.cached_build(), |event| {
            if event.verified.is_some() {
                project.stop_build();
            }
            events.push(event);
        });
        project.build(&mut builder);
        assert_eq!(builder.status, BuildStatus::Error);
        assert_eq!(
            (
                builder.searches_total,
                builder.hinted_searches,
                builder.hint_fallbacks,
                builder.goals_done
            ),
            (2, 1, 1, 1)
        );
        assert!(builder.cache().is_none());
    }
    assert_eq!(events.iter().filter(|e| e.verified.is_some()).count(), 1);
}

#[test]
fn full_and_hinted_counts_account_for_actual_attempts() {
    let mut project = learned();
    for (version, claim, expected) in [
        (1, "first and first", (1, 0, 1, 0)),
        (2, "second", (2, 1, 1, 1)),
    ] {
        edit(
            &mut project,
            &format!("{FACTS}theorem goal {{ {claim} }}"),
            version,
        );
        let mut builder = project.builder(|_| {});
        project.build(&mut builder);
        assert_eq!(builder.status, BuildStatus::Good);
        assert_eq!(
            (
                builder.searches_total,
                builder.full_searches(),
                builder.hinted_searches,
                builder.hint_fallbacks
            ),
            expected
        );
        assert_eq!(
            builder.full_searches() + builder.hinted_searches,
            builder.searches_total
        );
        assert_eq!((builder.num_success, builder.goals_done), (1, 1));
    }
    let mut warm = project.builder(|_| {});
    project.build(&mut warm);
    assert_eq!(warm.status, BuildStatus::Good);
    assert_eq!(
        (
            warm.searches_total,
            warm.full_searches(),
            warm.hinted_searches,
            warm.num_cached
        ),
        (0, 0, 0, 1)
    );
}
