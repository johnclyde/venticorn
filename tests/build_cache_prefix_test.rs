// Modified for Venticorn: partial reuse requires unchanged proof obligations and context.
use std::path::PathBuf;
use venticorn::builder::{BuildStatus, Builder};
use venticorn::module::ModuleRef;
use venticorn::project::{BuildReport, Project};

fn update(project: &mut Project, text: &str, version: i32) {
    project
        .update_file(PathBuf::from("/mock/main.ac"), text, version)
        .unwrap();
}

fn good(report: &BuildReport, fresh: i32, cached: i32) {
    assert_eq!(report.status, BuildStatus::Good, "{:?}", report.events);
    assert_eq!((report.num_success, report.num_cached), (fresh, cached));
    assert_eq!(report.goals_done, report.goals_total);
}

#[test]
fn middle_edit_reuses_only_the_unchanged_earlier_theorem() {
    let mut project = Project::new_mock();
    let original = "theorem one {\n true = true\n}\ntheorem two {\n true = true\n}\ntheorem three {\n true = true\n}";
    project.mock("/mock/main.ac", original);
    good(&project.sync_build_report(), 3, 0);
    update(
        &mut project,
        &original.replacen(
            "theorem two {\n true = true",
            "theorem two {\n false = false",
            1,
        ),
        1,
    );
    let changed = project.sync_build_report();
    good(&changed, 2, 1);
    assert_eq!(
        changed
            .events
            .iter()
            .filter_map(|event| event.verified)
            .collect::<Vec<_>>(),
        vec![(0, 2), (3, 5), (6, 8)]
    );
    good(&project.sync_build_report(), 0, 3);
}

#[test]
fn changed_proof_body_invalidates_its_earlier_child_and_parent() {
    let mut project = Project::new_mock();
    let original = "theorem outer { true } by {\n true\n true\n}\ntheorem later { true }";
    project.mock("/mock/main.ac", original);
    good(&project.sync_build_report(), 4, 0);
    update(
        &mut project,
        &original.replace("\n true\n}", "\n true != true\n}"),
        1,
    );
    assert!(
        !project
            .get_env_by_ref(&ModuleRef::Name("main".into()))
            .unwrap()
            .iter_goals()
            .next()
            .unwrap()
            .goal_context()
            .unwrap()
            .inconsistency_okay
    );
    let failed = project.sync_build_report();
    assert_eq!(failed.status, BuildStatus::Warning);
    assert_eq!(failed.num_cached, 0);
    assert!(failed.events.iter().any(|event| event.diagnostic.is_some()));
    // A warned module never replaces the earlier complete record.
    update(&mut project, original, 2);
    good(&project.sync_build_report(), 0, 4);
}

#[test]
fn removing_later_explicit_false_rechecks_earlier_inconsistency_policy() {
    let mut project = Project::new_mock();
    let original = "let b: Bool = axiom\nlet c: Bool = axiom\nif b != b {\n c\n false\n}";
    project.mock("/mock/main.ac", original);
    good(&project.sync_build_report(), 2, 0);
    update(
        &mut project,
        &original.replace("\n false\n", "\n // removed\n"),
        1,
    );
    let failed = project.sync_build_report();
    assert_eq!(failed.status, BuildStatus::Warning);
    assert_eq!((failed.num_success, failed.num_cached), (0, 0));
    assert!(failed.events.iter().any(|event| event
        .diagnostic
        .as_ref()
        .is_some_and(|d| d.message.contains("inconsistency"))));
}

#[test]
fn later_import_changes_invalidate_earlier_proof_context() {
    let mut project = Project::new_mock();
    project.mock(
        "/mock/base.ac",
        "type Item: axiom\nlet a: Item = axiom\nlet b: Item = axiom",
    );
    project.mock(
        "/mock/bridge.ac",
        "import base\naxiom connection { base.a = base.b }",
    );
    project.mock("/mock/empty.ac", "");
    let visible = "import base\nimport bridge\ntheorem earlier { base.a = base.b }\n";
    project.mock("/mock/main.ac", visible);
    good(&project.sync_build_report(), 1, 0);
    good(&project.sync_build_report(), 0, 1);
    // Moving the import after the theorem cannot retain its earlier authority.
    let later = "import base\ntheorem earlier { base.a = base.b }\nimport bridge\n";
    for (version, text) in [later.to_owned(), later.replace("bridge", "empty")]
        .into_iter()
        .enumerate()
    {
        update(&mut project, &text, version as i32 + 1);
        let failed = project.sync_build_report();
        assert_eq!(failed.status, BuildStatus::Warning);
        assert_eq!((failed.num_success, failed.num_cached), (0, 0));
        assert!(failed
            .events
            .iter()
            .any(|event| event.module == ModuleRef::Name("main".into())
                && event.diagnostic.is_some()));
    }
}

#[test]
fn unproved_earlier_goal_is_not_promoted_by_a_later_edit() {
    let mut project = Project::new_mock();
    let original = "theorem false_claim { false }\ntheorem later { true }";
    project.mock("/mock/main.ac", original);
    assert_eq!(project.sync_build_report().status, BuildStatus::Warning);
    update(
        &mut project,
        &original.replace("later { true }", "later { true = true }"),
        1,
    );
    let failed = project.sync_build_report();
    assert_eq!(failed.status, BuildStatus::Warning);
    assert_eq!((failed.num_success, failed.num_cached), (1, 0));
    assert!(!failed
        .events
        .iter()
        .any(|event| event.verified == Some((0, 0))));
}

#[test]
fn cancellation_during_partial_reuse_does_not_publish_a_partial_snapshot() {
    let mut project = Project::new_mock();
    let original = "theorem one { true }\ntheorem two { true }";
    project.mock("/mock/main.ac", original);
    good(&project.sync_build_report(), 2, 0);
    update(
        &mut project,
        &original.replace("two { true }", "two { true = true }"),
        1,
    );
    let prior = project.cached_build();
    let mut events = Vec::new();
    let mut builder = Builder::with_cache(prior.clone(), |event| {
        if event.verified.is_some() {
            project.stop_build();
        }
        events.push(event);
    });
    project.build(&mut builder);
    assert_eq!(builder.status, BuildStatus::Error);
    assert!(builder.cache().is_none());
    assert_eq!(builder.num_cached, 1);
    drop(builder);
    assert_eq!(
        events
            .iter()
            .filter(|event| event.verified.is_some())
            .count(),
        1
    );
    assert_eq!(
        project
            .cached_build()
            .get(&ModuleRef::Name("main".into()))
            .unwrap()
            .fingerprint(),
        prior
            .get(&ModuleRef::Name("main".into()))
            .unwrap()
            .fingerprint()
    );
    project.allow_build();
    good(&project.sync_build_report(), 1, 1);
}

#[test]
fn dependency_suffix_edit_reuses_its_prefix_but_rechecks_importers() {
    let mut project = Project::new_mock();
    project.mock("/mock/leaf.ac", "theorem leaf { true }\n// old\n");
    project.mock("/mock/middle.ac", "import leaf\ntheorem middle { true }\n");
    project.mock("/mock/main.ac", "import middle\ntheorem main { true }\n");
    good(&project.sync_build_report(), 3, 0);
    project
        .update_file(
            PathBuf::from("/mock/leaf.ac"),
            "theorem leaf { true }\n// changed\n",
            1,
        )
        .unwrap();
    good(&project.sync_build_report(), 2, 1);
}

#[test]
fn dataset_collection_bypasses_partial_hits() {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", "theorem one { true }\n// old\n");
    good(&project.sync_build_report(), 1, 0);
    update(&mut project, "theorem one { true }\n// changed\n", 1);
    let mut builder = project.builder(|_| {});
    builder.create_dataset();
    project.build(&mut builder);
    assert_eq!(builder.status, BuildStatus::Good);
    assert_eq!((builder.num_success, builder.num_cached), (1, 0));
}

#[test]
fn constrained_structure_body_and_existence_edits_recheck_all_obligations() {
    let mut project = Project::new_mock();
    let original = "type Item: axiom\nlet witness: Item = axiom\nlet allowed: Item -> Bool = axiom\naxiom { allowed(witness) }\nstructure Box {\n value: Item\n} constraint { allowed(value) } by {\n allowed(witness)\n true\n}\n";
    project.mock("/mock/main.ac", original);
    let first = project.sync_build_report();
    assert_eq!(first.status, BuildStatus::Good, "{:?}", first.events);
    assert_eq!(first.num_cached, 0);
    assert_eq!(
        (first.goals_done, first.goals_total, first.num_success),
        (3, 3, 3)
    );
    update(
        &mut project,
        &original.replace("\n true\n", "\n true != true\n"),
        1,
    );
    let failed_body = project.sync_build_report();
    assert_eq!(failed_body.status, BuildStatus::Warning);
    assert_eq!(failed_body.num_cached, 0);
    assert_eq!(failed_body.goals_done, 3);
    assert!(failed_body
        .events
        .iter()
        .any(|event| event
            .diagnostic
            .as_ref()
            .is_some_and(|d| d.range.start.line == 8)));
    update(&mut project, original, 2);
    good(&project.sync_build_report(), 0, first.goals_total);
    update(
        &mut project,
        &original.replace(
            "constraint { allowed(value) }",
            "constraint { allowed(value) and not allowed(value) }",
        ),
        3,
    );
    let impossible = project.sync_build_report();
    assert_eq!(impossible.status, BuildStatus::Warning);
    assert_eq!(impossible.num_cached, 0);
    assert!(!impossible
        .events
        .iter()
        .any(|event| event.verified == Some((4, 9))));
    assert_eq!(impossible.goals_done, 3);
    assert!(impossible
        .events
        .iter()
        .any(|event| event
            .diagnostic
            .as_ref()
            .is_some_and(|d| d.range.start.line == 6)));
}
