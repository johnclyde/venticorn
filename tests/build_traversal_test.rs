use std::path::PathBuf;
use venticorn::builder::{BuildStatus, Builder};
use venticorn::module::ModuleRef;
use venticorn::persistent_cache::CachePolicy;
use venticorn::project::Project;
use venticorn::prover::Outcome;

#[test]
fn build_matches_reference_postorder_for_nested_and_generated_obligations() {
    let mut project = Project::new_mock();
    project.set_cache_policy(CachePolicy::Disabled);
    project.mock("/mock/main.ac", "type Item: axiom\nlet x: Item = axiom\nlet y: Item = axiom\nlet chosen: Bool satisfy { chosen = true }\ntheorem goal(a: Item) { a != x or a != y or x = y } by {\n if a = x {\n  if a = y {\n   x = y\n  }\n  a != y or x = y\n }\n}\n");
    let env = project
        .get_env_by_ref(&ModuleRef::Name("main".into()))
        .unwrap();
    let mut slow = vec![];
    project.for_each_prover_slow(env, &mut |mut prover, goal| {
        slow.push((
            (goal.first_line, goal.last_line),
            prover.verification_search(),
        ));
        true
    });
    let mut fast = vec![];
    project.for_each_prover_fast(env, &mut |mut prover, goal| {
        fast.push((
            (goal.first_line, goal.last_line),
            prover.verification_search(),
        ));
        true
    });
    // The conditional blocks contribute scope, not separate goals: the four
    // obligations are satisfy, the two nested claims, and the containing theorem.
    assert_eq!(
        slow.iter().map(|(range, _)| *range).collect::<Vec<_>>(),
        vec![(3, 3), (7, 7), (9, 9), (4, 11)]
    );
    assert!(
        slow.iter().all(|(_, outcome)| *outcome == Outcome::Success),
        "{slow:?}"
    );
    assert_eq!(slow, fast);
    let report = project.sync_build_report();
    assert_eq!(report.status, BuildStatus::Good);
    assert_eq!(report.goals_done as usize, slow.len());
    assert_eq!(report.num_success as usize, slow.len());
    assert_eq!(report.num_cached, 0);
    assert_eq!(
        report
            .events
            .iter()
            .filter_map(|event| event.verified)
            .collect::<Vec<_>>(),
        slow.iter().map(|(range, _)| *range).collect::<Vec<_>>()
    );
}

#[test]
fn later_or_current_theorem_facts_cannot_verify_an_earlier_claim() {
    let mut project = Project::new_mock();
    project.mock(
        "/mock/main.ac",
        "let flag: Bool = axiom\ntheorem early { flag }\naxiom later { flag }\n",
    );
    let report = project.sync_build_report();
    assert_eq!(report.status, BuildStatus::Warning);
    assert_eq!(
        (report.num_success, report.num_cached, report.goals_done),
        (0, 0, 1)
    );
    assert!(!report.events.iter().any(|event| event.verified.is_some()));
    assert!(report.events.iter().any(|event| event.diagnostic.is_some()));
}

#[test]
fn cancellation_from_last_reused_child_stops_before_its_parent() {
    let mut project = Project::new_mock();
    let source = "theorem outer { true } by {\n true\n}\n";
    project.mock("/mock/main.ac", source);
    let prior = project.sync_build_report();
    assert_eq!(prior.status, BuildStatus::Good);
    project
        .update_file(
            PathBuf::from("/mock/main.ac"),
            &format!("{source}theorem extra {{ true }}\n"),
            1,
        )
        .unwrap();
    let mut verified = vec![];
    let mut builder = Builder::with_cache(prior.cache.unwrap(), |event| {
        if let Some(range) = event.verified {
            verified.push(range);
            project.stop_build();
        }
    });
    project.build(&mut builder);
    assert_eq!(builder.status, BuildStatus::Error);
    assert_eq!(
        (builder.num_success, builder.num_cached, builder.goals_done),
        (0, 1, 1)
    );
    assert!(builder.cache().is_none());
    drop(builder);
    assert_eq!(verified, vec![(1, 1)]);
}
