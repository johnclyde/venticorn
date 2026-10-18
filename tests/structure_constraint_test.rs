// Modified for Venticorn: constrained structures must preserve proof obligations and scope.
use venticorn::environment::Environment;
use venticorn::project::Project;
use venticorn::statement::{Statement, StatementInfo};

#[test]
fn constraint_syntax_retains_its_expression_and_closing_range() {
    let source =
        "structure Pair {\n first: Bool\n second: Bool\n} constraint {\n first or second\n}";
    let statement = Statement::parse_str(source).unwrap();
    assert_eq!(statement.range().end.line, 5);
    assert_eq!(statement.range().end.character, 1);
    match &statement.statement {
        StatementInfo::Structure(structure) => {
            assert_eq!(
                structure.constraint.as_ref().unwrap().to_string(),
                "first or second"
            );
        }
        _ => panic!("expected structure"),
    }
    assert_eq!(
        Statement::parse_str(&statement.to_string())
            .unwrap()
            .to_string(),
        statement.to_string()
    );
}

#[test]
fn constrained_structures_create_an_earlier_scoped_existence_obligation() {
    use venticorn::acorn_value::AcornValue;
    let mut env = Environment::new_test();
    env.add("structure Pair {\n first: Bool\n second: Bool\n} constraint {\n first or second\n} by {\n true or true\n}");
    assert_eq!(env.iter_goals().count(), 2);
    assert!(!env.nodes[0].is_structural());
    let block = env.nodes[0].block.as_ref().unwrap();
    assert!(
        matches!(block.goal.as_ref().unwrap().value(), AcornValue::Exists(fields, _) if fields.len() == 2)
    );
    assert!(!block.env.bindings.has_type_name("Pair"));
    assert!(!block.env.bindings.has_identifier("Pair.new"));
    assert!(!env.bindings.has_identifier("first"));
    assert!(!env.bindings.has_identifier("second"));
    assert!(env.nodes.iter().skip(1).all(|node| node.is_structural()));
    env.check_lines();
}

#[test]
fn malformed_structures_do_not_retain_names_nodes_or_line_metadata() {
    for source in [
        "structure Pair {\n first: Bool\n} constraint { missing }",
        "structure Pair {\n first: Bool\n} constraint { first } by { missing }",
        "structure Pair {\n first: Bool\n} constraint { first } by { Pair.new(true).first }",
        "structure Pair {\n first: Bool\n first: Bool\n} constraint { first }",
        "structure Pair {\n new: Bool\n} constraint { true }",
        "structure Pair {\n first: Missing\n} constraint { true }",
    ] {
        let mut env = Environment::new_test();
        env.add("theorem prior { true }");
        let count = env.nodes.len();
        let last_line = env.last_line();
        let statement = Statement::parse_str(source).unwrap();
        env.add_statement(&mut Project::new_mock(), &statement)
            .unwrap_err();
        assert_eq!(env.nodes.len(), count, "{source}");
        assert_eq!(env.last_line(), last_line, "{source}");
        assert!(!env.bindings.has_type_name("Pair"));
        for name in ["Pair.new", "Pair.first", "first"] {
            assert!(
                !env.bindings.has_identifier(name),
                "{source}: leaked {name}"
            );
        }
        env.add("structure Pair {\n first: Bool\n}");
        assert!(env.bindings.has_identifier("Pair.new"));
    }
}

#[test]
fn constrained_constructors_remain_callable_but_cannot_be_match_patterns() {
    let mut env = Environment::new_test();
    env.add("structure Pair {\n first: Bool\n second: Bool\n} constraint { first and second }");
    env.add("let pair: Pair = Pair.new(false, false)");
    let statement = Statement::parse_str(
        "define recover(p: Pair) -> Bool { match p { Pair.new(a, b) { a } } }",
    )
    .unwrap();
    let error = env
        .add_statement(&mut Project::new_mock(), &statement)
        .unwrap_err();
    assert!(
        error.message().contains("expected a constructor"),
        "{error}"
    );
    assert!(!env.bindings.has_identifier("recover"));
    let mut ordinary = Environment::new_test();
    ordinary.add("structure Pair {\n first: Bool\n second: Bool\n}\ndefine recover(p: Pair) -> Bool { match p { Pair.new(a, b) { a } } }");
    assert!(ordinary.bindings.has_identifier("recover"));
}

#[test]
fn constrained_projection_equations_are_conditional_and_inputs_need_not_be_injective() {
    use venticorn::acorn_value::{AcornValue, BinaryOp};
    use venticorn::prover::{Outcome, Prover};
    let text = "type Item: axiom\nlet a: Item = axiom\nlet b: Item = axiom\nlet witness: Item = axiom\nlet allowed: Item -> Bool = axiom\naxiom { a != b }\naxiom { not allowed(a) }\naxiom { not allowed(b) }\naxiom { allowed(witness) }\nstructure Box {\n value: Item\n} constraint { allowed(value) }\ntheorem goal { Box.new(a) != Box.new(b) }";
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", text);
    let id = project.expect_ok("main");
    let env = project.get_env_by_id(id).unwrap();
    assert_eq!(env.nodes.iter().filter(|node| {
        node.is_structural() && matches!(&node.claim.value, AcornValue::ForAll(_, body) if matches!(&**body, AcornValue::Binary(BinaryOp::Implies, _, _)))
    }).count(), 1);
    let node = env.get_node_by_name("goal");
    let mut prover = Prover::new(&project, false);
    for fact in node.usable_facts(&project) {
        prover.add_fact(fact);
    }
    prover.set_goal(&node.goal_context().unwrap());
    assert_eq!(
        prover.quick_verification_search(),
        Outcome::Exhausted,
        "{:?}",
        prover.error()
    );
}

fn proof_outcomes(source: &str) -> Vec<venticorn::prover::Outcome> {
    use venticorn::prover::{Outcome, Prover};
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", source);
    let id = project.expect_ok("main");
    let env = project.get_env_by_id(id).unwrap();
    env.nodes
        .iter()
        .for_each(|node| node.claim.value.validate().unwrap());
    env.iter_goals()
        .map(|node| {
            let mut prover = Prover::new(&project, false);
            for fact in node.usable_facts(&project) {
                prover.add_fact(fact);
            }
            prover.set_goal(&node.goal_context().unwrap());
            let outcome = prover.quick_verification_search();
            assert!(
                !matches!(outcome, Outcome::Error(_)),
                "{:?}",
                prover.error()
            );
            outcome
        })
        .collect()
}

#[test]
fn instance_constraints_preserve_nested_quantifier_variable_scopes() {
    use venticorn::prover::Outcome;
    let source = "type Item: axiom\ntype Tag: axiom\nlet witness: Item = axiom\nlet related: (Item, Tag) -> Bool = axiom\naxiom(tag: Tag) { related(witness, tag) }\nstructure Box {\n value: Item\n} constraint {\n forall(tag: Tag) { related(value, tag) }\n}\ntheorem goal(box: Box, tag: Tag) { related(box.value, tag) }";
    assert_eq!(
        proof_outcomes(source),
        vec![Outcome::Success, Outcome::Success]
    );
}

#[test]
fn a_constraint_cannot_prove_its_own_nonemptiness() {
    use venticorn::prover::Outcome;
    assert_eq!(
        proof_outcomes("structure Empty {\n value: Bool\n} constraint { false }"),
        vec![Outcome::Exhausted]
    );
}

#[test]
fn constraint_and_body_lines_select_the_correct_scoped_goals() {
    use venticorn::block::NodeCursor;
    for (body, end) in [("", 4), (" by {\n true\n}", 6)] {
        let source =
            format!("structure Flag {{\n value: Bool\n}} constraint {{\n value = value\n}}{body}");
        let mut env = Environment::new_test();
        env.add(&source);
        let path = env.path_for_line(3).unwrap();
        let context = NodeCursor::from_path(&env, &path).goal_context().unwrap();
        assert_eq!((context.first_line, context.last_line), (0, end));
        assert_eq!(env.path_for_line(end).unwrap(), path);
        assert!(env.path_for_line(end + 1).is_err());
        env.check_lines();
    }
}
