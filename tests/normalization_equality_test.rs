use venticorn::acorn_type::AcornType;
use venticorn::acorn_value::AcornValue;
use venticorn::builder::BuildStatus;
use venticorn::module::FIRST_NORMAL;
use venticorn::normalizer::Normalizer;
use venticorn::project::Project;
use venticorn::prover::Outcome;

#[test]
fn constant_equality_stays_explicit_with_known_right_hand_side() {
    let data = AcornType::Data(FIRST_NORMAL, "Value".into(), vec![]);
    for typ in [
        data.clone(),
        AcornType::new_functional(vec![data.clone()], data),
    ] {
        for local in [false, true] {
            let left = AcornValue::new_constant(FIRST_NORMAL, "left".into(), vec![], typ.clone());
            let right = AcornValue::new_constant(FIRST_NORMAL, "right".into(), vec![], typ.clone());
            let mut normalizer = Normalizer::new();
            let right_term = normalizer.term_from_value(&right, local).unwrap();
            let equality = AcornValue::new_equals(left.clone(), right.clone());
            let clauses = normalizer.normalize(&equality, local).expect_clauses();
            assert!(
                !clauses.is_empty(),
                "equality must not vanish into an atom alias"
            );
            assert!(clauses.iter().all(|clause| !clause.literals.is_empty()));
            assert_ne!(
                normalizer.term_from_value(&left, local).unwrap(),
                right_term
            );
            assert_eq!(
                normalizer.normalize(&equality, local).expect_clauses(),
                clauses
            );
        }
    }
}

fn outcomes(source: &str, shallow: bool) -> Vec<Outcome> {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", source);
    let module = project.expect_ok("main");
    let env = project.get_env_by_id(module).unwrap();
    let expected = env.iter_goals().count();
    assert!(expected > 0);
    let mut results = vec![];
    project.for_each_prover_slow(env, &mut |mut prover, _| {
        let result = if shallow {
            prover.quick_verification_search()
        } else {
            prover.quick_search()
        };
        assert!(!matches!(result, Outcome::Error(_)), "{:?}", prover.error());
        results.push(result);
        true
    });
    assert_eq!(results.len(), expected);
    results
}

#[test]
fn explicit_equality_and_language_alias_replay_nonempty_proof_at_original_position() {
    let source = "structure Marker<T> {\n value: Bool\n}\n\
        class Marker<T> {\n define chosen(self) -> Marker<T> { axiom }\n}\n\
        let seed: Marker<Bool> = axiom\n\
        let alternate: Marker<Bool> = axiom\n\
        let alias: Marker<Bool> = alternate\n\
        let combine: (Marker<Bool>, Marker<Bool>) -> Marker<Bool> = axiom\n\
        define marked(n: Marker<Bool>) -> Bool { exists(d: Marker<Bool>) { combine(seed, d) = n } }\n\
        axiom same_seed { alternate = seed }\n\
        axiom marker_right(a: Marker<Bool>, b: Marker<Bool>) { b = seed.chosen -> combine(a, b) = seed.chosen }\n\
        theorem goal { marked(alias.chosen) }\n\
        let future_alias: Marker<Bool> = alternate\n\
        theorem after { true }";
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", source);
    let module = project.expect_ok("main");
    let env = project.get_env_by_id(module).unwrap();
    assert_eq!(env.iter_goals().count(), 2);
    assert_eq!(
        env.bindings.get_constant_value("alias"),
        env.bindings.get_constant_value("alternate")
    );
    let node = env.get_node_by_name("goal");
    let goal = node.goal_context().unwrap();
    let mut prover = project.prover_for_node(&node, false);
    prover.set_goal(&goal);
    assert_eq!(
        prover.quick_search(),
        Outcome::Success,
        "{:?}",
        prover.error()
    );
    let names = prover.get_useful_fact_names().unwrap();
    assert!(names.contains(&(module, "same_seed".into())), "{names:?}");
    assert!(names.contains(&(module, "marked".into())), "{names:?}");
    let code = prover
        .get_condensed_proof()
        .unwrap()
        .to_code(&node.bindings_for_codegen())
        .unwrap();
    assert!(!code.is_empty(), "the witness must emit a real proof body");
    assert!(!code.join("\n").contains("future_alias"));
    let lines = source.lines().collect::<Vec<_>>();
    let insertion = goal.proof_insertion_line as usize;
    assert!(goal.insert_block);
    assert_eq!(lines[insertion], "theorem goal { marked(alias.chosen) }");
    let suffix = lines[insertion + 1..].join("\n");
    assert!(suffix.starts_with("let future_alias"));
    let insert = |body: &str| {
        format!(
            "{} by {{\n{body}\n}}\n{suffix}",
            lines[..=insertion].join("\n")
        )
    };
    let replay = insert(&code.join("\n"));
    assert!(replay.ends_with("theorem after { true }"));
    for shallow in [false, true] {
        assert!(outcomes(&replay, shallow)
            .iter()
            .all(|o| *o == Outcome::Success));
    }
    let false_replay = insert("exists(x: Marker<Bool>) { x != x }");
    assert!(matches!(
        outcomes(&false_replay, false)[0],
        Outcome::Exhausted | Outcome::Constrained | Outcome::Timeout
    ));
    assert_eq!(outcomes(&false_replay, true)[0], Outcome::Exhausted);
    let mut invalid = Project::new_mock();
    invalid.mock("/mock/main.ac", &false_replay);
    let module = invalid.expect_ok("main");
    let first = invalid
        .get_env_by_id(module)
        .unwrap()
        .iter_goals()
        .next()
        .unwrap()
        .goal_context()
        .unwrap();
    assert_eq!(first.goal.range().start.line, insertion as u32 + 1);
    let report = invalid.sync_build_report();
    assert_eq!(report.status, BuildStatus::Warning);
    assert!(report.goals_done >= 3);
    assert!(report.num_success < report.goals_total);
    assert_eq!(invalid.cached_build().num_modules(), 0);
}
