use venticorn::acorn_type::AcornType;
use venticorn::acorn_value::AcornValue;
use venticorn::expression::Expression;
use venticorn::project::Project;
use venticorn::prover::{Outcome, Prover};

const DECLARATIONS: &str = "structure Pair<T, U> {\n first: T\n second: U\n}\n\
    define double<T>(x: T) -> Pair<T, T> { Pair.new(x, x) }\n\
    define first<Z, A>(left: Z, right: A) -> Z { left }\n\
    define phantom<Z, A>(flag: Bool) -> Bool { flag }\n\
    define witness<T> -> T { axiom }\n\
    define identity<T>(value: T) -> T { value }\n";

fn project(source: &str) -> Project {
    let mut project = Project::new_mock();
    project.mock("/mock/pair.ac", DECLARATIONS);
    project.mock("/mock/other.ac", DECLARATIONS);
    project.mock(
        "/mock/bridge.ac",
        "from pair import double, first, phantom, witness, identity",
    );
    project.mock("/mock/main.ac", source);
    project
}

#[test]
fn direct_generic_imports_keep_canonical_identity_and_order_through_reexports() {
    for module in ["pair", "bridge"] {
        let mut project = project(&format!(
            "from {module} import double, first, phantom, witness, identity\nimport other"
        ));
        let id = project.expect_ok("main");
        let defining_id = project.load_module_by_name("pair").unwrap();
        let env = project.get_env_by_id(id).unwrap();
        for text in [
            "double(true)",
            "double(identity<Bool>)",
            "first(true, identity<Bool>)",
            "first<Bool, Bool -> Bool>(true)",
            "first<Bool, Bool -> Bool>",
            "phantom<Bool, Bool -> Bool>(true)",
            "witness<(Bool -> Bool) -> Bool>",
            "identity<(Bool -> Bool)>(identity<Bool>)(true)",
        ] {
            let value = env
                .bindings
                .evaluate_value(&project, &Expression::expect_value(text), None)
                .unwrap();
            value.validate().unwrap();
            let code = env.bindings.value_to_code(&value).unwrap();
            if text == "double(true)" {
                assert_eq!(code, text);
            }
            if text.starts_with("phantom")
                || text.starts_with("first<")
                || text.starts_with("witness")
            {
                assert!(code.contains('<'), "required actuals lost: {code}");
            }
            let replay = env
                .bindings
                .evaluate_value(&project, &Expression::expect_value(&code), None)
                .unwrap();
            assert_eq!(value, replay, "{text} rendered as {code}");
        }
        let value = env
            .bindings
            .evaluate_value(
                &project,
                &Expression::expect_value("first(true, identity<Bool>)"),
                None,
            )
            .unwrap();
        let AcornValue::Application(application) = value else {
            panic!("expected application")
        };
        let AcornValue::Constant(constant) = *application.function else {
            panic!("expected resolved constant")
        };
        assert_eq!(constant.name.module_id, defining_id);
        assert_eq!(constant.name.local_name.to_string(), "first");
        assert_eq!(
            constant.params,
            vec![
                AcornType::Bool,
                AcornType::new_functional(vec![AcornType::Bool], AcornType::Bool)
            ]
        );
        let other = env
            .bindings
            .evaluate_value(
                &project,
                &Expression::expect_value("other.first(true, identity<Bool>)"),
                None,
            )
            .unwrap();
        let AcornValue::Application(other) = other else {
            panic!("expected application")
        };
        let AcornValue::Constant(other) = *other.function else {
            panic!("expected resolved constant")
        };
        assert_ne!(constant.name.module_id, other.name.module_id);
    }
}

#[test]
fn direct_generic_imports_retain_located_inference_errors_and_pending_boundaries() {
    let mut project = project("from pair import double, first, phantom, witness, identity");
    let id = project.expect_ok("main");
    let env = project.get_env_by_id(id).unwrap();
    for text in [
        "double",
        "double<Bool, Bool>(true)",
        "double<Bool>(identity<Bool>)",
        "double(true, true)",
        "phantom(true)",
        "first<Bool, Bool>(true)",
        "witness",
    ] {
        // A partial application is a valid function, but cannot satisfy a Bool result.
        let expected = if text == "first<Bool, Bool>(true)" {
            Some(&AcornType::Bool)
        } else {
            None
        };
        let error = env
            .bindings
            .evaluate_value(&project, &Expression::expect_value(text), expected)
            .unwrap_err();
        assert!(
            error.range().end.character > error.range().start.character,
            "{error}"
        );
    }
    let labels = env.bindings.get_completions(&project, "", true).unwrap();
    assert!(!labels.iter().any(|item| item.label == "double"));
}

fn witness_project(source: &str) -> Project {
    let mut project = Project::new_mock();
    project.mock("/mock/marker.ac", "structure Marker<T> {\n value: Bool\n}\ndefine chosen<T>(seed: Marker<T>) -> Marker<T> { axiom }");
    project.mock(
        "/mock/main.ac",
        &format!("from marker import Marker, chosen\n{source}"),
    );
    project
}

fn verify_witness(source: &str) -> Outcome {
    let mut project = witness_project(source);
    let id = project.expect_ok("main");
    for node in project.get_env_by_id(id).unwrap().iter_goals() {
        let mut prover = Prover::new(&project, false);
        for fact in node.usable_facts(&project) {
            prover.add_fact(fact);
        }
        prover.set_goal(&node.goal_context().unwrap());
        let outcome = prover.quick_verification_search();
        assert_ne!(outcome, Outcome::Error, "{:?}", prover.error);
        if outcome != Outcome::Success {
            return outcome;
        }
    }
    Outcome::Success
}

#[test]
fn inferred_imported_generic_witnesses_generate_nonempty_replayable_proofs() {
    for actual in ["Bool", "(Bool -> Bool) -> Bool"] {
        let source = format!(
            "let k0: Bool = true\n\
             let seed: Marker<{actual}> = axiom\n\
             let mul: (Marker<{actual}>, Marker<{actual}>) -> Marker<{actual}> = axiom\n\
             define marked(n: Marker<{actual}>) -> Bool {{ exists(d: Marker<{actual}>) {{ mul(seed, d) = n }} }}\n\
             axiom marker_right(a: Marker<{actual}>, b: Marker<{actual}>) {{ b = chosen(seed) -> mul(a, b) = chosen(seed) }}\n\
             theorem goal {{ marked(chosen(seed)) }}"
        );
        let mut project = witness_project(&source);
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
        let code = code.join("\n");
        assert!(code.contains("chosen(seed)"), "{code}");
        assert!(!code.contains("let k0:"), "{code}");
        assert_eq!(
            verify_witness(&format!("{source} by {{\n{code}\n}}")),
            Outcome::Success
        );
        assert_eq!(
            verify_witness(&format!(
                "{source} by {{ exists(p: Marker<{actual}>) {{ p != p }} }}"
            )),
            Outcome::Exhausted
        );
    }
}
