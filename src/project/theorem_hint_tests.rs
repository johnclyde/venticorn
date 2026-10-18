use super::*;

fn named(name: &str) -> ModuleRef {
    ModuleRef::Name(name.into())
}
fn premise(module: &str, names: &[&str]) -> PremiseSet {
    PremiseSet::from([(named(module), names.iter().map(|s| s.to_string()).collect())])
}
fn pair(project: &Project, premises: &PremiseSet) -> (Prover, Option<Prover>, GoalContext) {
    let env = project.get_env_by_ref(&named("main")).unwrap();
    let node = env.get_node_by_name("goal");
    let goal = node.goal_context().unwrap();
    let mut full = Prover::new(project, false);
    for fact in node.usable_facts(project) {
        full.add_fact(fact);
    }
    full.set_goal(&goal);
    let mut guided = project.make_guided_prover(env, &node, premises);
    if let Some(guided) = &mut guided {
        guided.set_goal(&goal);
    }
    (full, guided, goal)
}

#[test]
fn hint_eligibility_does_not_require_verified_dependencies() {
    let mut project = Project::new_mock();
    project.mock(
        "/mock/leaf.ac",
        "let seed: Bool = axiom\nlet flag: Bool = axiom\naxiom start { seed }\naxiom known { seed implies flag }",
    );
    project.mock("/mock/middle.ac", "import leaf\nlet flag: Bool = leaf.flag");
    project.mock(
        "/mock/main.ac",
        "import middle\ntheorem goal { middle.flag }",
    );
    // Imported modules are admitted but not targets and have no verified snapshot.
    project.targets = HashSet::from([named("main")]);
    let mut cold = project.builder(|_| {});
    project.build(&mut cold);
    assert_eq!(cold.status, BuildStatus::Good);
    assert_eq!(cold.cache().unwrap().num_modules(), 1);
    project
        .update_file(
            PathBuf::from("/mock/leaf.ac"),
            "let seed: Bool = axiom\nlet flag: Bool = axiom\naxiom start { seed }\naxiom known { seed implies (flag and flag) }",
            1,
        )
        .unwrap();
    project.targets = HashSet::from([named("main")]);
    let mut edited = project.builder(|_| {});
    project.build(&mut edited);
    assert_eq!(edited.status, BuildStatus::Good);
    assert_eq!(
        (
            edited.searches_total,
            edited.hinted_searches,
            edited.hinted_successes,
            edited.num_cached
        ),
        (1, 1, 1, 0)
    );
}

#[test]
fn resolver_never_loads_missing_self_or_future_facts_and_keeps_module_identity() {
    let mut project = Project::new_mock();
    project.mock(
        "/mock/left.ac",
        "let flag: Bool = axiom\naxiom same { flag }",
    );
    project.mock(
        "/mock/right.ac",
        "let flag: Bool = axiom\naxiom same { flag }",
    );
    project.mock(
        "/mock/main.ac",
        "import left\nimport right\ntheorem goal { right.flag }\naxiom future { right.flag }",
    );
    for missing in [
        premise("main", &["future"]),
        premise("left", &["absent"]),
        premise("absent", &["same"]),
    ] {
        assert!(pair(&project, &missing).1.is_none(), "{missing:?}");
    }
    // The implicit body has an identity definition named goal. Recognizing that
    // metadata must never load the theorem itself into the initial subset.
    let (_, Some(mut self_hint), _) = pair(&project, &premise("main", &["goal"])) else {
        panic!()
    };
    assert_eq!(self_hint.verification_search(), Outcome::Exhausted);
    let (_, Some(mut wrong), _) = pair(&project, &premise("left", &["same"])) else {
        panic!()
    };
    assert_eq!(wrong.verification_search(), Outcome::Exhausted);
    let (_, Some(mut right), _) = pair(&project, &premise("right", &["same"])) else {
        panic!()
    };
    assert_eq!(right.verification_search(), Outcome::Success);
}

#[test]
fn terminal_hint_errors_and_presearch_cancellation_do_not_fallback() {
    let mut project = Project::new_mock();
    project.mock(
        "/mock/main.ac",
        "let seed: Bool = axiom\nlet flag: Bool = axiom\naxiom start { seed }\naxiom known { seed implies flag }\ntheorem goal { flag }",
    );
    let (full, Some(mut guided), goal) = pair(&project, &premise("main", &["known"])) else {
        panic!()
    };
    guided.error = Some("test an already-reported normalizer error".into());
    let mut builder = Builder::new(|_| {});
    let result = project
        .search_goal(full, Some(guided), &mut builder)
        .unwrap();
    assert_eq!(
        result.outcome,
        Outcome::Error("test an already-reported normalizer error".into())
    );
    assert!(result.hinted);
    builder.finish_search(&result.prover, &goal, result.outcome, result.elapsed);
    assert_eq!(
        (
            builder.hinted_searches,
            builder.hint_fallbacks,
            builder.searches_total,
            builder.goals_done
        ),
        (1, 0, 1, 1)
    );
    assert_eq!(builder.status, BuildStatus::Error);
    let (full, Some(mut guided), goal) = pair(&project, &premise("main", &["known"])) else {
        panic!()
    };
    guided.stop_flags.push(Arc::new(AtomicBool::new(true)));
    let mut interrupted = Builder::new(|_| {});
    let result = project
        .search_goal(full, Some(guided), &mut interrupted)
        .unwrap();
    assert_eq!(result.outcome, Outcome::Interrupted);
    interrupted.finish_search(&result.prover, &goal, result.outcome, result.elapsed);
    assert_eq!(
        (
            interrupted.hinted_searches,
            interrupted.hint_fallbacks,
            interrupted.searches_total,
            interrupted.goals_done
        ),
        (1, 0, 1, 1)
    );
    assert_eq!(interrupted.status, BuildStatus::Error);
    let (full, guided, _) = pair(&project, &premise("main", &["known"]));
    project.stop_build();
    let mut cancelled = Builder::new(|_| {});
    assert!(project.search_goal(full, guided, &mut cancelled).is_none());
    assert_eq!(
        (
            cancelled.hinted_searches,
            cancelled.hint_fallbacks,
            cancelled.searches_total,
            cancelled.goals_done
        ),
        (0, 0, 0, 0)
    );
}

#[test]
fn imported_generic_guided_proofs_emit_nonempty_replayable_code() {
    let dependency = "structure Marker<T> {\n value: Bool\n}\ndefine chosen<T>(seed: Marker<T>) -> Marker<T> { axiom }";
    let source = "from marker import Marker, chosen\n\
        let k0: Bool = true\n\
        let seed: Marker<(Bool -> Bool) -> Bool> = axiom\n\
        let mul: (Marker<(Bool -> Bool) -> Bool>, Marker<(Bool -> Bool) -> Bool>) -> Marker<(Bool -> Bool) -> Bool> = axiom\n\
        define marked(n: Marker<(Bool -> Bool) -> Bool>) -> Bool { exists(d: Marker<(Bool -> Bool) -> Bool>) { mul(seed, d) = n } }\n\
        axiom marker_right(a: Marker<(Bool -> Bool) -> Bool>, b: Marker<(Bool -> Bool) -> Bool>) { b = chosen(seed) -> mul(a, b) = chosen(seed) }\n\
        theorem goal { marked(chosen(seed)) }";
    let mut project = Project::new_mock();
    project.mock("/mock/marker.ac", dependency);
    project.mock("/mock/main.ac", source);
    let learned = project.sync_build_report();
    assert_eq!(learned.status, BuildStatus::Good);
    let cache = learned.cache.unwrap();
    let hints = &cache.get(&named("main")).unwrap().theorem_premises()["goal"];
    let (full, guided, _) = pair(&project, hints);
    assert!(guided.is_some());
    let mut builder = Builder::new(|_| {});
    let search = project.search_goal(full, guided, &mut builder).unwrap();
    assert_eq!(search.outcome, Outcome::Success);
    assert!(search.hinted);
    assert_eq!(builder.hint_fallbacks, 0);
    let env = project.get_env_by_ref(&named("main")).unwrap();
    let code = search
        .prover
        .get_condensed_proof()
        .unwrap()
        .to_code(&env.bindings)
        .unwrap();
    assert!(!code.is_empty());
    let code = code.join("\n");
    assert!(code.contains("chosen(seed)"), "{code}");
    assert!(!code.contains("let k0:"), "{code}");
    for (body, expected) in [
        (code, BuildStatus::Good),
        (
            "exists(p: Marker<(Bool -> Bool) -> Bool>) { p != p }".into(),
            BuildStatus::Warning,
        ),
    ] {
        let mut replay = Project::new_mock();
        replay.mock("/mock/marker.ac", dependency);
        replay.mock("/mock/main.ac", &format!("{source} by {{\n{body}\n}}"));
        let result = replay.sync_build_report();
        assert_eq!(result.status, expected);
    }
}

#[test]
fn selected_shared_datatype_and_anonymous_sources_keep_all_facts() {
    let mut project = Project::new_mock();
    project.mock(
        "/mock/choice.ac",
        "inductive Choice {\n one\n two\n three\n}\nlet flag: Bool = axiom\naxiom { flag }",
    );
    project.mock("/mock/main.ac", "from choice import Choice, flag\ntheorem goal { Choice.one != Choice.three and Choice.two != Choice.three and flag }");
    let hints = premise("choice", &["Choice.three", "7"]);
    let (_, Some(mut guided), _) = pair(&project, &hints) else {
        panic!()
    };
    assert_eq!(guided.verification_search(), Outcome::Success);
    let names = project.collect_theorem_premises(&guided).unwrap();
    assert!(names[&named("choice")].contains("Choice.three"));
    assert!(names[&named("choice")].contains("7"));
}
