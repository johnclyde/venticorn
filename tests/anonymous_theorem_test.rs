// Modified for Venticorn: anonymous declarations must retain proof obligations and source identity.
use venticorn::environment::Environment;
use venticorn::project::Project;
use venticorn::statement::Statement;

#[test]
fn anonymous_theorems_create_goals_without_leaking_parameter_bindings() {
    let mut env = Environment::new_test();
    for (i, source) in [
        "theorem { true }",
        "theorem(a: Bool, b: Bool) { a = b or a or b }",
        "theorem<T>(value: T) { value = value }",
    ]
    .iter()
    .enumerate()
    {
        let statement = Statement::parse_str(source).unwrap();
        env.add_statement(&mut Project::new_mock(), &statement)
            .unwrap();
        assert_eq!(env.nodes.len(), i + 1);
        assert_eq!(env.iter_goals().count(), i + 1);
        let node = env.nodes.last().unwrap();
        assert!(!node.is_structural());
        assert!(node.proposition().name().is_none());
        assert_eq!(
            node.proposition().source.description(),
            "an anonymous theorem"
        );
        assert!(!env.bindings.has_identifier("a"));
        assert!(!env.bindings.has_identifier("b"));
        assert!(!env.bindings.has_type_name("T"));
    }
}

#[test]
fn theorem_goal_ranges_end_at_the_claim_not_the_proof_body() {
    let mut env = Environment::new_test();
    env.add("theorem named(b: Bool) {\n    b or not b\n} by {\n    true\n}\n");
    let node = env.nodes.last().unwrap();
    let range = node.proposition().source.range;
    assert_eq!(range.start.line, 0);
    assert_eq!(range.start.character, 0);
    assert_eq!(range.end.line, 2);
    assert_eq!(range.end.character, 1);
    let context = env.iter_goals().last().unwrap().goal_context().unwrap();
    match context.goal {
        venticorn::goal::Goal::Prove(proposition) => assert_eq!(proposition.source.range, range),
        _ => panic!("expected theorem proof goal"),
    }
}

#[test]
fn malformed_theorem_bodies_leave_no_names_ranges_or_facts() {
    for source in [
        "theorem broken { true } by { missing }",
        "theorem { true } by { missing }",
        "theorem broken<T>(value: T) { value = value } by { missing }",
        "theorem<T>(value: T) { value = value } by { missing }",
    ] {
        let mut env = Environment::new_test();
        let statement = Statement::parse_str(source).unwrap();
        let error = env
            .add_statement(&mut Project::new_mock(), &statement)
            .unwrap_err();
        assert!(error.message().contains("missing"), "{error}");
        assert!(env.nodes.is_empty());
        assert!(!env.bindings.has_identifier("broken"));
        assert!(!env.bindings.has_identifier("value"));
        assert!(!env.bindings.has_type_name("T"));
        env.add("theorem broken { true }");
        assert_eq!(env.nodes.len(), 1);
    }
}

#[test]
fn theorem_parameter_collisions_are_errors_instead_of_panics() {
    for source in [
        "theorem f(f: Bool) { f or not f }",
        "theorem f<f>(value: f) { value = value }",
    ] {
        let mut env = Environment::new_test();
        let statement = Statement::parse_str(source).unwrap();
        let error = env
            .add_statement(&mut Project::new_mock(), &statement)
            .unwrap_err();
        assert_eq!(error.message(), "theorem name conflicts with a parameter");
        assert!(env.nodes.is_empty());
        assert!(!env.bindings.has_identifier("f"));
        assert!(!env.bindings.has_type_name("f"));
        env.add("theorem f { true }");
    }
}

#[test]
fn anonymous_goal_names_have_a_source_location_fallback() {
    let mut env = Environment::new_test();
    env.add("inductive Choice {\n first\n second\n}\ntheorem { match Choice.first { Choice.first { true } Choice.second { false } } }");
    let context = env.iter_goals().last().unwrap().goal_context().unwrap();
    assert_eq!(context.name, "claim at line 5");
}

#[test]
fn anonymous_axioms_are_explicit_assumptions_with_scoped_parameters() {
    let mut env = Environment::new_test();
    for (i, source) in [
        "axiom { not false }",
        "axiom(value: Bool) { value or not value }",
        "axiom<T>(value: T) { value = value }",
    ]
    .iter()
    .enumerate()
    {
        let statement = Statement::parse_str(source).unwrap();
        env.add_statement(&mut Project::new_mock(), &statement)
            .unwrap();
        assert_eq!(env.nodes.len(), i + 1);
        assert_eq!(env.iter_goals().count(), 0);
        let node = env.nodes.last().unwrap();
        assert!(node.is_structural());
        assert!(node.proposition().name().is_none());
        assert!(node.proposition().source.is_axiom());
        assert_eq!(
            node.proposition().source.description(),
            "an anonymous axiom"
        );
        assert!(!env.bindings.has_identifier("value"));
        assert!(!env.bindings.has_type_name("T"));
    }
}

#[test]
fn axiom_proof_blocks_are_rejected_without_discarding_their_content() {
    for source in [
        "axiom assumption { true } by { false }",
        "axiom { true } by { false }",
    ] {
        let mut env = Environment::new_test();
        let statement = Statement::parse_str(source).unwrap();
        let error = env
            .add_statement(&mut Project::new_mock(), &statement)
            .unwrap_err();
        assert_eq!(error.message(), "axioms cannot have proof blocks");
        assert!(env.nodes.is_empty());
        assert!(!env.bindings.has_identifier("assumption"));
    }
}

#[test]
fn theorem_citations_preserve_theorem_rather_than_axiom_provenance() {
    let mut env = Environment::new_test();
    env.add("axiom foundation(value: Bool) { value or not value }\ntheorem cited(value: Bool) { foundation(value) }\ntheorem(value: Bool) { cited(value) }");
    assert_eq!(env.iter_goals().count(), 0);
    assert!(env.nodes[0].proposition().source.is_axiom());
    assert!(!env.nodes[1].proposition().source.is_axiom());
    assert!(!env.nodes[2].proposition().source.is_axiom());
    assert_eq!(env.nodes[1].proposition().name(), Some("cited"));
    assert_eq!(env.nodes[2].proposition().name(), None);
}

#[test]
fn anonymous_claim_selection_preserves_distinct_source_ranges() {
    let mut env = Environment::new_test();
    env.add("theorem {\ntrue\n} by {\ntrue\n}\ntheorem(value: Bool) {\nvalue or not value\n}\naxiom { true }\n");
    for (line, index, first, last) in [(1, 0, 0, 2), (6, 1, 5, 7)] {
        let path = env.path_for_line(line).unwrap();
        assert_eq!(path, vec![index]);
        let range = env.nodes[index].proposition().source.range;
        assert_eq!((range.start.line, range.start.character), (first, 0));
        assert_eq!((range.end.line, range.end.character), (last, 1));
        let cursor = venticorn::block::NodeCursor::from_path(&env, &path);
        match cursor.goal_context().unwrap().goal {
            venticorn::goal::Goal::Prove(proposition) => {
                assert_eq!(proposition.source.range, range)
            }
            _ => panic!("expected theorem proof goal"),
        }
    }
    assert_eq!(env.path_for_line(8).unwrap_err(), "line 9 is an axiom");
}
