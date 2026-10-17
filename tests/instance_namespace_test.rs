use venticorn::acorn_type::AcornType;
use venticorn::acorn_value::AcornValue;
use venticorn::environment::Environment;
use venticorn::expression::Expression;
use venticorn::project::Project;
use venticorn::prover::{Outcome, Prover};
use venticorn::statement::Statement;

const DECLARATION: &str = "typeclass T: Marked {\n flag: Bool\n}\ninductive State {\n clean\n}\ninstance State: Marked {\n let flag: Bool = true\n}";

#[test]
fn canonical_namespaces_roundtrip_without_cross_module_collisions() {
    let mut project = Project::new_mock();
    project.mock("/mock/left.ac", DECLARATION);
    project.mock("/mock/right.ac", &DECLARATION.replace("= true", "= false"));
    project.mock(
        "/mock/main.ac",
        "from left import State\nimport right\ntype Alias: right.State",
    );
    let id = project.expect_ok("main");
    let left = project.expect_ok("left");
    let env = project.get_env_by_id(id).unwrap();
    let mut values = vec![];
    for (input, expected) in [
        ("State.Marked.flag", "State.Marked.flag"),
        ("Alias.Marked.flag", "Alias.Marked.flag"),
    ] {
        let value = env
            .bindings
            .evaluate_value(&project, &Expression::expect_value(input), None)
            .unwrap();
        let code = env.bindings.value_to_code(&value).unwrap();
        assert_eq!(code, expected);
        assert_eq!(
            env.bindings
                .evaluate_value(&project, &Expression::expect_value(&code), None)
                .unwrap(),
            value
        );
        values.push(value);
    }
    assert_ne!(values[0], values[1]);
    for input in [
        "State.Missing.flag",
        "State.Marked.missing",
        "State.Marked",
        "State.Marked.flag.extra",
    ] {
        assert!(
            env.bindings
                .evaluate_value(&project, &Expression::expect_value(input), None)
                .is_err(),
            "{input}"
        );
    }
    for name in [
        "State.Missing.flag",
        "State.Marked.missing",
        "State.Marked.flag.extra",
    ] {
        let fabricated = AcornValue::new_constant(left, name.to_string(), vec![], AcornType::Bool);
        assert!(env.bindings.value_to_code(&fabricated).is_err(), "{name}");
    }
}

#[test]
fn type_attributes_do_not_silently_shadow_registered_namespaces() {
    let mut env = Environment::new_test();
    env.add(DECLARATION);
    // Source declarations reject uppercase member identifiers. Exercise the
    // defensive namespace collision guard through the lower-level binding API.
    env.bad("class State { let Marked: Bool = true }");
    env.bindings
        .add_constant("State.Marked", vec![], AcornType::Bool, None, None);
    let error = env
        .add_statement(
            &mut Project::new_mock(),
            &Statement::parse_str("let value: Bool = State.Marked.flag").unwrap(),
        )
        .unwrap_err();
    assert_eq!(
        error.message(),
        "ambiguous type attribute and instance namespace"
    );
    assert!(!env.bindings.name_in_use("value"));
    let member = env
        .bindings
        .get_constant_value("State.Marked.flag")
        .unwrap()
        .resolved()
        .unwrap();
    assert!(env.bindings.value_to_code(&member).is_err());
}

fn verify(source: &str, ordinary: bool) -> Outcome {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", source);
    let id = project.expect_ok("main");
    for node in project.get_env_by_id(id).unwrap().iter_goals() {
        let mut prover = Prover::new(&project, false);
        for fact in node.usable_facts(&project) {
            prover.add_fact(fact);
        }
        prover.set_goal(&node.goal_context().unwrap());
        let result = if ordinary {
            prover.quick_search()
        } else {
            prover.quick_verification_search()
        };
        assert_ne!(result, Outcome::Error);
        if result != Outcome::Success {
            return result;
        }
    }
    Outcome::Success
}

#[test]
fn concrete_instance_witness_emits_nonempty_replayable_proof() {
    let source = "typeclass T: Marked {\n chosen: T\n mul: (T, T) -> T\n}\ninductive State {\n clean\n dirty\n}\ninstance State: Marked {\n let chosen: State = axiom\n define mul(self, other: State) -> State { axiom }\n}\ndefine marked(n: State) -> Bool { exists(d: State) { State.Marked.mul(State.clean, d) = n } }\naxiom chosen_right(a: State, b: State) { b = State.Marked.chosen -> State.Marked.mul(a, b) = State.Marked.chosen }\ntheorem goal { marked(State.Marked.chosen) }";
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", source);
    let id = project.expect_ok("main");
    let env = project.get_env_by_id(id).unwrap();
    let node = env.get_node_by_name("goal");
    let mut prover = Prover::new(&project, false);
    for fact in node.usable_facts(&project) {
        prover.add_fact(fact);
    }
    prover.set_goal(&node.goal_context().unwrap());
    assert_eq!(prover.quick_search(), Outcome::Success);
    let code = prover
        .get_and_print_proof()
        .unwrap()
        .to_code(&env.bindings)
        .unwrap();
    assert!(!code.is_empty());
    assert!(code.join("\n").contains("State.Marked.chosen"), "{code:?}");
    assert_eq!(
        verify(&format!("{source} by {{\n{}\n}}", code.join("\n")), false),
        Outcome::Success
    );
    assert_eq!(
        verify(
            &format!("{source} by {{ exists(x: State) {{ x != x }} }}"),
            false
        ),
        Outcome::Exhausted
    );
    let false_body = format!("{source} by {{ exists(x: State) {{ x != x }} }}");
    assert!(matches!(
        verify(&false_body, true),
        Outcome::Exhausted | Outcome::Timeout | Outcome::Constrained
    ));
}

#[test]
fn reexported_type_alias_retains_its_canonical_instance_namespace() {
    let mut project = Project::new_mock();
    project.mock("/mock/owner.ac", DECLARATION);
    project.mock("/mock/bridge.ac", "from owner import State");
    project.mock("/mock/main.ac", "from bridge import State");
    let id = project.expect_ok("main");
    let env = project.get_env_by_id(id).unwrap();
    let input = "State.Marked.flag";
    let value = env
        .bindings
        .evaluate_value(&project, &Expression::expect_value(input), None)
        .unwrap();
    let code = env.bindings.value_to_code(&value).unwrap();
    assert_eq!(code, input);
    assert_eq!(
        env.bindings
            .evaluate_value(&project, &Expression::expect_value(&code), None)
            .unwrap(),
        value
    );
}
