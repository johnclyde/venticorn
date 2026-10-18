use std::collections::HashMap;
use venticorn::acorn_type::Class;
use venticorn::acorn_type::{AcornType, TypeParam, Typeclass};
use venticorn::environment::Environment;
use venticorn::project::Project;
use venticorn::prover::{Outcome, Prover};
use venticorn::statement::Statement;

const CLASSES: &str = "typeclass M: Magma {\n mul: (M, M) -> M\n flag: Bool\n chosen: M -> M\n}\ntypeclass N: Other {\n value: N\n}\n";

fn prove(source: &str) -> Outcome {
    run_search(source, false)
}

// An ordinary bounded search may time out without deciding a false claim.
// Keep that same-path control separate from the shallow exhaustive rejection.
fn reject_false(source: &str) {
    assert!(matches!(
        prove(source),
        Outcome::Exhausted | Outcome::Timeout | Outcome::Constrained
    ));
    assert_eq!(verify_shallow(source), Outcome::Exhausted);
}

fn verify_shallow(source: &str) -> Outcome {
    run_search(source, true)
}

fn run_search(source: &str, shallow: bool) -> Outcome {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", source);
    let id = project.expect_ok("main");
    let mut result = Outcome::Success;
    for node in project.get_env_by_id(id).unwrap().iter_goals() {
        let mut prover = Prover::new(&project, false);
        for fact in node.usable_facts(&project) {
            fact.as_proposition().unwrap().value.validate().unwrap();
            prover.add_fact(fact);
        }
        let goal = node.goal_context().unwrap();
        assert!(!goal.goal.value().is_generic());
        prover.set_goal(&goal);
        result = if shallow {
            prover.quick_verification_search()
        } else {
            prover.quick_search()
        };
        assert!(!matches!(result, Outcome::Error(_)), "{:?}", prover.error());
        if result != Outcome::Success {
            return result;
        }
    }
    result
}

#[test]
fn bound_matching_checks_new_and_already_mapped_parameters() {
    let class = Typeclass {
        module_id: 10,
        name: "Magma".into(),
    };
    let formal = TypeParam {
        name: "T".into(),
        typeclass: Some(class.clone()),
    };
    let bounded = AcornType::Variable(formal.clone());
    for actual in [
        AcornType::Bool,
        AcornType::Data(Class::new(10, "Item".into()), vec![]),
        AcornType::new_functional(vec![AcornType::Bool], AcornType::Bool),
        AcornType::Variable(TypeParam::unconstrained("U")),
        AcornType::Arbitrary(TypeParam::unconstrained("U")),
        AcornType::Arbitrary(TypeParam {
            name: "U".into(),
            typeclass: Some(Typeclass {
                module_id: 11,
                name: "Magma".into(),
            }),
        }),
    ] {
        assert!(!bounded.match_instance(&actual, &mut HashMap::new()));
        let mut mapped = HashMap::from([("T".to_string(), actual.clone())]);
        assert!(!bounded.match_instance(&actual, &mut mapped));
    }
    for actual in [
        AcornType::Variable(formal.clone()),
        AcornType::Arbitrary(formal),
    ] {
        let mut mapped = HashMap::new();
        assert!(bounded.match_instance(&actual, &mut mapped));
        assert!(bounded.match_instance(&actual, &mut mapped));
        assert_eq!(bounded.instantiate(&[("T".into(), actual.clone())]), actual);
    }
    let mixed = AcornType::new_functional(
        vec![AcornType::Variable(TypeParam::unconstrained("T")), bounded],
        AcornType::Bool,
    );
    let bad = AcornType::new_functional(vec![AcornType::Bool, AcornType::Bool], AcornType::Bool);
    assert!(!mixed.match_instance(&bad, &mut HashMap::new()));
}

#[test]
fn phantom_explicit_inferred_and_partial_calls_preserve_formal_bounds() {
    let mut env = Environment::new_test();
    env.add(CLASSES);
    env.add("define phantom<T: Magma> -> Bool { true }\ndefine partial<T: Magma>(a: T) -> (T -> T) { Magma.mul(a) }\ndefine use<T: Magma>(a: T) -> T { partial(a)(a) }\ndefine flags<T: Magma> -> Bool { phantom<T> and Magma.flag<T> }");
    for source in [
        "let bad: Bool = phantom<Bool>",
        "let bad: Bool = Magma.flag<Bool>",
        "let bad: Bool = Magma.mul<Bool>(true, true)",
        "let bad: Bool = Magma.mul(true, true)",
        "define bad<U>(a: U) -> U { Magma.mul(a)(a) }",
        "define bad<U: Other>(a: U) -> U { Magma.mul<U>(a, a) }",
        "define bad<U: Other>(a: U) -> U { Magma.mul(a, a) }",
        "define bad<U: Other> -> Bool { phantom<U> }",
    ] {
        let error = env
            .add_statement(
                &mut Project::new_mock(),
                &Statement::parse_str(source).unwrap(),
            )
            .unwrap_err();
        assert!(
            error.message().contains("class bound") || error.message().contains("expected type"),
            "{error}"
        );
        assert!(!env.bindings.name_in_use("bad"));
        assert!(!env.bindings.name_in_use("U"));
    }
    let class = env.bindings.get_typeclass_for_name("Magma").unwrap();
    for name in ["phantom", "Magma.flag", "partial", "use", "flags"] {
        let params = env.bindings.get_params(name);
        assert_eq!(params.len(), 1);
        assert_eq!(params[0].typeclass.as_ref(), Some(class));
    }
    assert_eq!(prove(&format!("{CLASSES}define identity<T: Magma>(a: T) -> T {{ a }}\ntheorem goal<T: Magma>(a: T) {{ identity(a) = a }}")), Outcome::Success);
    reject_false(&format!("{CLASSES}define identity<T: Magma>(a: T) -> T {{ a }}\ntheorem goal<T: Magma>(a: T) {{ identity(a) != a }}"));
}

#[test]
fn imports_and_aliases_keep_phantom_bounds_and_defining_module_identity() {
    let mut project = Project::new_mock();
    project.mock(
        "/mock/left.ac",
        &format!("{CLASSES}define phantom<T: Magma> -> Bool {{ true }}"),
    );
    project.mock("/mock/right.ac", CLASSES);
    project.mock(
        "/mock/main.ac",
        "from left import phantom\nimport right\ndefine good<T: left.Magma> -> Bool { phantom<T> }",
    );
    let id = project.expect_ok("main");
    let mut env = project.get_env_by_id(id).unwrap().child(0, false);
    for source in [
        "let bad: Bool = phantom<Bool>",
        "define bad<T: right.Magma> -> Bool { phantom<T> }",
    ] {
        let error = env
            .add_statement(&mut project, &Statement::parse_str(source).unwrap())
            .unwrap_err();
        assert!(error.message().contains("class bound"), "{error}");
        assert!(!env.bindings.name_in_use("bad"));
    }
}

#[test]
fn recursion_and_identity_facts_keep_ordered_phantom_class_formals() {
    let source = format!("{CLASSES}inductive Nat {{\n zero\n suc(Nat)\n}}\ndefine repeat<T: Magma, U: Other>(n: Nat, value: T) -> T {{ match n {{\n Nat.zero {{ value }}\n Nat.suc(previous) {{ repeat<T, U>(previous, value) }}\n}} }}");
    let mut env = Environment::new_test();
    env.add(&source);
    let (body, params) = env.bindings.get_definition_and_params("repeat").unwrap();
    assert_eq!(
        params
            .iter()
            .map(|p| (p.name.as_str(), p.typeclass.as_ref().unwrap().name.as_str()))
            .collect::<Vec<_>>(),
        [("T", "Magma"), ("U", "Other")]
    );
    let expected = params
        .iter()
        .cloned()
        .map(AcornType::Variable)
        .collect::<Vec<_>>();
    let mut recursive = vec![];
    body.find_constants(
        &|c| c.name.local_name.to_string() == "repeat",
        &mut recursive,
    );
    assert!(!recursive.is_empty());
    for constant in recursive {
        assert_eq!(constant.params, expected);
    }
    let mut identity = vec![];
    for node in &env.nodes {
        node.claim.value.find_constants(
            &|c| c.name.local_name.to_string() == "repeat",
            &mut identity,
        );
    }
    assert!(!identity.is_empty());
    for constant in identity {
        assert_eq!(constant.params, expected);
    }
    assert_eq!(prove(&format!("{source}\ntheorem goal<T: Magma, U: Other>(value: T) {{ repeat<T, U>(Nat.suc(Nat.zero), value) = value }}")), Outcome::Success);
}

#[test]
fn erased_theorem_bounds_and_undemanded_phantom_axioms_cannot_prove_false() {
    let mut env = Environment::new_test();
    env.add(CLASSES);
    env.add("theorem always<T> { true }");
    for source in [
        "axiom bad<T: Magma> { false }",
        "axiom bad<T: Magma> { always<T> }",
        "theorem bad<T: Magma> { always<T> }",
        "theorem bad<T: Magma> { true } by { forall(x: T) { x = x } }",
    ] {
        let nodes = env.nodes.len();
        let error = env
            .add_statement(
                &mut Project::new_mock(),
                &Statement::parse_str(source).unwrap(),
            )
            .unwrap_err();
        assert!(
            error
                .message()
                .contains("must occur in the exported proposition"),
            "{error}"
        );
        assert_eq!(env.nodes.len(), nodes);
        assert!(!env.bindings.name_in_use("bad"));
        assert!(!env.bindings.name_in_use("T"));
        assert!(!env.includes_explicit_false);
    }
    let source = format!("{CLASSES}define phantom<T: Magma> -> Bool {{ false }}\naxiom hypothetical<T: Magma> {{ phantom<T> }}\ntheorem goal {{ false }}");
    assert_eq!(prove(&source), Outcome::Exhausted);
}

#[test]
fn bounded_witness_proof_emits_nonempty_code_and_replays_with_false_control() {
    let source = "typeclass M: Magma {\n mul: (M, M) -> M\n seed: M\n chosen: M\n}\ndefine marked<T: Magma>(n: T) -> Bool { exists(d: T) { Magma.mul(Magma.seed<T>, d) = n } }\naxiom chosen_right<T: Magma>(a: T, b: T) { b = Magma.chosen<T> -> Magma.mul(a, b) = Magma.chosen<T> }\ntheorem goal<T: Magma> { marked(Magma.chosen<T>) }";
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", &source);
    let id = project.expect_ok("main");
    let env = project.get_env_by_id(id).unwrap();
    let node = env.get_node_by_name("goal");
    let mut prover = Prover::new(&project, false);
    for fact in node.usable_facts(&project) {
        prover.add_fact(fact);
    }
    prover.set_goal(&node.goal_context().unwrap());
    assert_eq!(prover.quick_search(), Outcome::Success);
    let scope = &node.current().block.as_ref().unwrap().env.bindings;
    let code = prover
        .get_and_print_proof()
        .unwrap()
        .to_code(scope)
        .unwrap();
    assert!(!code.is_empty(), "actual generated proof text is required");
    assert_eq!(
        prove(&format!("{source} by {{\n{}\n}}", code.join("\n"))),
        Outcome::Success
    );
    reject_false(&format!("{source} by {{ exists(x: T) {{ x != x }} }}"));
}
