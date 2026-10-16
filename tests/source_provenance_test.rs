use tower_lsp::lsp_types::{Position, Range};
use venticorn::acorn_type::AcornType;
use venticorn::acorn_value::AcornValue;
use venticorn::environment::Environment;
use venticorn::project::Project;
use venticorn::proposition::{Proposition, SourceType};
use venticorn::prover::{Outcome, Prover};

#[test]
fn definition_source_names_survive_generic_instantiation() {
    let mut env = Environment::new_test();
    env.add("define identity<T>(value: T) -> T { value }");
    let fact = env
        .exported_facts()
        .into_iter()
        .find(|fact| fact.source.name().as_deref() == Some("identity"))
        .unwrap();
    let generic_description = fact.source.description();
    for actual in [
        AcornType::Bool,
        AcornType::new_functional(vec![AcornType::Bool], AcornType::Bool),
    ] {
        let specialized = fact.instantiate(&[("T".into(), actual.clone())]);
        specialized.value.validate().unwrap();
        assert_eq!(specialized.source.name().as_deref(), Some("identity"));
        assert_eq!(specialized.source.module, fact.source.module);
        assert_eq!(specialized.source.range, fact.source.range);
        let SourceType::ConstantDefinition(AcornValue::Constant(constant), name) =
            &specialized.source.source_type
        else {
            panic!("missing constant provenance")
        };
        assert_eq!(name, "identity");
        assert_eq!(constant.params, vec![actual]);
        assert_ne!(specialized.source.description(), generic_description);
    }
}

#[test]
fn datatype_sources_name_members_and_keep_shared_principles() {
    let mut env = Environment::new_test();
    env.add("structure Pair<T, U> {\n first: T\n second: U\n}\nstructure Checked<T> {\n value: T\n} constraint { value = value }\ninductive Choice {\n one\n two\n three\n}");
    let names = env
        .exported_facts()
        .iter()
        .filter_map(|fact| fact.source.name())
        .collect::<Vec<_>>();
    for expected in [
        "Pair.new",
        "Pair.first",
        "Pair.second",
        "Checked.constraint",
        "Checked.new",
        "Checked.value",
        "Choice.new",
        "Choice.two",
        "Choice.three",
    ] {
        assert!(
            names.iter().any(|name| name == expected),
            "missing {expected}: {names:?}"
        );
    }
    assert_eq!(
        names
            .iter()
            .filter(|name| name.as_str() == "Choice.three")
            .count(),
        2
    );
    assert!(!names.iter().any(|name| name.contains("Choice.Choice")));
}

#[test]
fn stable_source_identifiers_are_separate_from_human_descriptions() {
    let range = Range::new(Position::new(2, 0), Position::new(2, 4));
    let anonymous = Proposition::anonymous(AcornValue::Bool(true), 1, range);
    assert_eq!(anonymous.source.name().as_deref(), Some("3"));
    assert_eq!(anonymous.source.description(), "line 3");
    assert_eq!(
        anonymous
            .with_negated_goal(AcornValue::Bool(false))
            .source
            .name(),
        None
    );
    assert_eq!(
        Proposition::premise(AcornValue::Bool(true), 1, range)
            .source
            .name(),
        None
    );
    let mut env = Environment::new_test();
    env.add("theorem named { true }");
    let old = env.get_node_by_name("named").goal_context().unwrap();
    let new = env.get_node_by_description("named").goal_context().unwrap();
    assert_eq!(new.description(), old.name);
    assert_eq!(new.goal.value(), old.goal.value());
}

#[test]
fn functional_definitions_and_substitutions_keep_their_original_proofs() {
    for (declarations, claim) in [
        ("", "is_min(gcd_term(p)) = f"),
        (
            "define find(f: Nat -> Bool) -> Nat { axiom }",
            "find(is_min(gcd_term(p))) = find(f)",
        ),
    ] {
        let source = format!("type Nat: axiom\n{declarations}\ndefine is_min(f: Nat -> Bool) -> (Nat -> Bool) {{ axiom }}\ndefine gcd_term(p: Nat) -> (Nat -> Bool) {{ axiom }}\nlet p: Nat = axiom\nlet f: Nat -> Bool = is_min(gcd_term(p))\ntheorem goal {{ {claim} }}");
        let mut project = Project::new_mock();
        project.mock("/mock/main.ac", &source);
        let id = project.expect_ok("main");
        for node in project.get_env_by_id(id).unwrap().iter_goals() {
            for shallow in [true, false] {
                let mut prover = Prover::new(&project, false);
                for fact in node.usable_facts(&project) {
                    prover.add_fact(fact);
                }
                prover.set_goal(&node.goal_context().unwrap());
                let outcome = if shallow {
                    prover.quick_shallow_search()
                } else {
                    prover.verification_search()
                };
                assert_eq!(outcome, Outcome::Success, "{claim}: {:?}", prover.error);
            }
        }
    }
}
