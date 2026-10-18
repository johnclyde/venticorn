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
        .find(|fact| fact.proposition.source.name().as_deref() == Some("identity"))
        .unwrap();
    let generic_description = fact.proposition.source.description();
    for actual in [
        AcornType::Bool,
        AcornType::new_functional(vec![AcornType::Bool], AcornType::Bool),
    ] {
        let specialized = fact.instantiate(&[("T".into(), actual.clone())]);
        specialized.proposition.value.validate().unwrap();
        assert_eq!(
            specialized.proposition.source.name().as_deref(),
            Some("identity")
        );
        assert_eq!(
            specialized.proposition.source.module,
            fact.proposition.source.module
        );
        assert_eq!(
            specialized.proposition.source.qualified_name(),
            Some((fact.proposition.source.module, "identity".into()))
        );
        assert_eq!(
            specialized.proposition.source.range,
            fact.proposition.source.range
        );
        let SourceType::ConstantDefinition(AcornValue::Constant(constant), name) =
            &specialized.proposition.source.source_type
        else {
            panic!("missing constant provenance")
        };
        assert_eq!(name, "identity");
        assert_eq!(constant.params, vec![actual]);
        assert_ne!(
            specialized.proposition.source.description(),
            generic_description
        );
    }
}

#[test]
fn datatype_sources_name_members_and_keep_shared_principles() {
    let mut env = Environment::new_test();
    env.add("structure Pair<T, U> {\n first: T\n second: U\n}\nstructure Checked<T> {\n value: T\n} constraint { value = value }\ninductive Choice {\n one\n two\n three\n}");
    let names = env
        .exported_facts()
        .iter()
        .filter_map(|fact| fact.proposition.source.name())
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
    assert_eq!(anonymous.source.qualified_name(), Some((1, "3".into())));
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
                assert_eq!(outcome, Outcome::Success, "{claim}: {:?}", prover.error());
            }
        }
    }
}

#[test]
fn theorem_names_are_distinct_from_fact_selection_names() {
    let mut env = Environment::new_test();
    env.add("define identity(value: Bool) -> Bool { value }\naxiom named_axiom { true }\ntheorem named_theorem { true }\naxiom { true }");
    for node in &env.nodes {
        assert_eq!(node.claim.name(), node.claim.theorem_name());
        match node.claim.source.name().as_deref() {
            Some("identity") => assert_eq!(node.claim.theorem_name(), None),
            Some("named_axiom") => assert_eq!(node.claim.theorem_name(), Some("named_axiom")),
            Some("named_theorem") => assert_eq!(node.claim.theorem_name(), Some("named_theorem")),
            Some("4") => assert_eq!(node.claim.theorem_name(), None),
            unexpected => panic!("unexpected fact source: {unexpected:?}"),
        }
    }
    assert!(env.get_theorem_claim("identity").is_none());
    assert!(env.get_theorem_claim("named_axiom").is_some());
    assert!(env.get_theorem_claim("named_theorem").is_some());
    assert!(env.get_theorem_claim("4").is_none());
}

#[test]
fn instance_relationships_keep_stable_names_and_separate_member_sources() {
    use venticorn::builder::BuildStatus;
    use venticorn::module::ModuleRef;

    let range = Range::new(Position::new(3, 0), Position::new(8, 1));
    let marker = Proposition::instance(None, 1, range, "Item".into(), "Marked".into());
    assert_eq!(marker.value, AcornValue::Bool(true));
    assert_eq!(marker.source.range, range);
    assert_eq!(
        marker.source.description(),
        "the 'Item: Marked' relationship"
    );
    assert_eq!(
        marker.source.fact_name().as_deref(),
        Some("Item.instance.Marked")
    );
    assert_eq!(
        marker.source.qualified_fact_name(),
        Some((1, "Item.instance.Marked".into()))
    );
    let explicit = Proposition::instance(
        Some(AcornValue::Bool(false)),
        1,
        range,
        "Item".into(),
        "Marked".into(),
    );
    assert_eq!(explicit.value, AcornValue::Bool(false));
    assert_eq!(explicit.source, marker.source);

    let source = "type Item: axiom\nlet p: Item -> Bool = axiom\nlet chosen: Item = axiom\naxiom known { p(chosen) }\ntypeclass T: Marked {\n relation: T -> Bool\n value: T\n found { exists(x: T) { T.relation(x) and x = T.value } }\n}\ninstance Item: Marked {\n let relation: Item -> Bool = p\n let value: Item = chosen\n}\ntheorem after { Marked.relation(Marked.value<Item>) }";
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", source);
    let module = project.expect_ok("main");
    let env = project.get_env_by_id(module).unwrap();
    assert_eq!(env.iter_goals().count(), 2);
    let relationship = env.nodes.iter().find(|node| matches!(&node.claim.source.source_type, SourceType::Instance(name, class) if name == "Item" && class == "Marked")).unwrap();
    assert_eq!(relationship.claim.value, AcornValue::Bool(true));
    assert!(relationship.block.as_ref().unwrap().goal.is_some());
    let names = env
        .nodes
        .iter()
        .filter_map(|node| node.claim.source.fact_name())
        .collect::<Vec<_>>();
    for name in [
        "Item.instance.Marked",
        "Item.instance.Marked.relation",
        "Item.instance.Marked.value",
    ] {
        assert_eq!(
            names
                .iter()
                .filter(|actual| actual.as_str() == name)
                .count(),
            1
        );
    }
    let cold = project.sync_build_report();
    assert_eq!(cold.status, BuildStatus::Good);
    assert_eq!((cold.num_success, cold.num_cached), (2, 0));
    let main = ModuleRef::Name("main".into());
    let key = "Item.instance.Marked";
    let advice = cold.cache.unwrap().get(&main).unwrap().block_premises()[key].clone();
    assert!(!advice.is_empty());
    let warm = project.sync_build_report();
    assert_eq!(warm.status, BuildStatus::Good);
    assert_eq!((warm.num_success, warm.num_cached), (0, 2));
    assert_eq!(
        warm.cache.unwrap().get(&main).unwrap().block_premises()[key],
        advice
    );
    project.check_hashes = false;
    let mut guided = project.builder(|_| {});
    project.build(&mut guided);
    assert_eq!(guided.status, BuildStatus::Good);
    assert_eq!((guided.num_success, guided.num_cached), (2, 0));
    assert!(guided.hinted_searches > 0 && guided.hinted_successes > 0);
    assert_eq!(
        guided.cache().unwrap().get(&main).unwrap().block_premises()[key],
        advice
    );

    let false_source = source.replace(
        "let relation: Item -> Bool = p",
        "let relation: Item -> Bool = function(x: Item) { false }",
    );
    project.mock("/mock/main.ac", &false_source);
    let module = project.expect_ok("main");
    let obligation = project
        .get_env_by_id(module)
        .unwrap()
        .iter_goals()
        .next()
        .unwrap();
    let goal = obligation.goal_context().unwrap();
    let mut shallow = project.prover_for_node(&obligation, false);
    shallow.set_goal(&goal);
    assert_eq!(shallow.quick_shallow_search(), Outcome::Exhausted);
    let mut ordinary = project.prover_for_node(&obligation, false);
    ordinary.set_goal(&goal);
    assert!(matches!(
        ordinary.quick_search(),
        Outcome::Exhausted | Outcome::Constrained | Outcome::Timeout
    ));
    let rejected = project.sync_build_report();
    assert_eq!(rejected.status, BuildStatus::Warning);
    assert!(rejected.cache.unwrap().get(&main).is_none());
}
