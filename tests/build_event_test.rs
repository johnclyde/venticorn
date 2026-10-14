// Modified for Venticorn: build identity and verified-goal event regressions.
use venticorn::builder::BuildStatus;
use venticorn::module::ModuleRef;
use venticorn::project::Project;

#[test]
fn builds_have_distinct_ids_and_preserve_verified_goal_identity() {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", "theorem identity { true }");
    let (status, first) = project.sync_build();
    assert_eq!(status, BuildStatus::Good);
    let first_id = first[0].build_id;
    assert_ne!(first_id, 0);
    assert!(first.iter().all(|event| event.build_id == first_id));
    let verified: Vec<_> = first
        .iter()
        .filter(|event| event.verified.is_some())
        .collect();
    assert_eq!(verified.len(), 1);
    assert_eq!(verified[0].module, ModuleRef::Name("main".to_string()));
    assert_eq!(verified[0].verified.unwrap().0, 0);
    let (_, second) = project.sync_build();
    assert!(second
        .iter()
        .all(|event| event.build_id != first_id && event.build_id != 0));
}

#[test]
fn a_failed_claim_does_not_emit_a_verified_range() {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", "theorem impossible { false }");
    let (status, events) = project.sync_build();
    assert_eq!(status, BuildStatus::Warning);
    assert!(events.iter().all(|event| event.verified.is_none()));
}

#[test]
fn slow_success_keeps_its_verified_range() {
    use std::time::Duration;
    use venticorn::builder::Builder;
    use venticorn::prover::{Outcome, Prover};

    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", "theorem identity { true }");
    let module = ModuleRef::Name("main".to_string());
    let environment = project.get_env_by_ref(&module).unwrap();
    let node = environment.iter_goals().next().unwrap();
    let goal = node.goal_context().unwrap();
    let mut prover = Prover::new(&project, false);
    for fact in node.usable_facts(&project) {
        prover.add_fact(fact);
    }
    prover.set_goal(&goal);
    assert_eq!(prover.quick_search(), Outcome::Success);
    let mut events = Vec::new();
    {
        let mut builder = Builder::new(|event| events.push(event));
        builder.log_when_slow = true;
        builder.module_loaded(environment);
        builder.module_proving_started(&module);
        builder.search_finished(&prover, &goal, Outcome::Success, Duration::from_secs(1));
    }
    assert_eq!(events.len(), 1);
    assert!(events[0].log_message.as_ref().unwrap().contains("took"));
    assert_eq!(events[0].module, module);
    assert_eq!(
        events[0].verified.unwrap(),
        (goal.first_line, goal.last_line)
    );
    assert_eq!(events[0].progress, Some((1, 1)));
}

#[test]
fn successful_goal_events_cover_the_entire_proof_block() {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", "theorem outer { true } by {\n true\n}\n");
    let (status, events) = project.sync_build();
    assert_eq!(status, BuildStatus::Good);
    assert_eq!(
        events
            .iter()
            .filter_map(|event| event.verified)
            .collect::<Vec<_>>(),
        vec![(1, 1), (0, 2)]
    );
}
