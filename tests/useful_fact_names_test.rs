use std::collections::BTreeSet;
use venticorn::module::{ModuleId, ModuleRef};
use venticorn::project::Project;
use venticorn::prover::{Outcome, Prover};

fn prove(project: &Project, module: ModuleId, name: &str) -> Prover {
    let node = project
        .get_env_by_id(module)
        .unwrap()
        .get_node_by_name(name);
    let mut prover = Prover::new(project, false);
    for fact in node.usable_facts(project) {
        prover.add_fact(fact);
    }
    prover.set_goal(&node.goal_context().unwrap());
    assert_eq!(
        prover.quick_search(),
        Outcome::Success,
        "{:?}",
        prover.error()
    );
    prover
}

#[test]
fn useful_facts_keep_defining_modules_and_exclude_unused_assumptions() {
    let mut project = Project::new_mock();
    for module in ["left", "right"] {
        project.mock(
            &format!("/mock/{module}.ac"),
            "let flag: Bool = axiom\nlet spare: Bool = axiom\naxiom same { flag }\naxiom unused { spare }",
        );
    }
    project.mock(
        "/mock/main.ac",
        "import left\nimport right\ntheorem goal { left.flag and right.flag }",
    );
    let id = project.expect_ok("main");
    let expected = ["left", "right"]
        .into_iter()
        .map(|name| {
            (
                project
                    .get_env_by_ref(&ModuleRef::Name(name.into()))
                    .unwrap()
                    .module_id,
                "same".into(),
            )
        })
        .collect::<BTreeSet<_>>();
    let prover = prove(&project, id, "goal");
    assert_eq!(prover.get_useful_fact_names(), Some(expected));
}

#[test]
fn specialized_definitions_keep_their_declared_qualified_identity() {
    let mut project = Project::new_mock();
    project.mock(
        "/mock/generic.ac",
        "define identity<T>(value: T) -> T { value }",
    );
    project.mock(
        "/mock/main.ac",
        "from generic import identity\ntheorem goal(x: Bool) { identity(x) = x }",
    );
    let id = project.expect_ok("main");
    let defining_id = project
        .get_env_by_ref(&ModuleRef::Name("generic".into()))
        .unwrap()
        .module_id;
    let prover = prove(&project, id, "goal");
    assert_eq!(
        prover.get_useful_fact_names(),
        Some(BTreeSet::from([(defining_id, "identity".into())]))
    );
}

#[test]
fn missing_proofs_and_proofs_without_named_facts_are_distinct() {
    let mut project = Project::new_mock();
    project.mock(
        "/mock/main.ac",
        "theorem true_goal { true }\ntheorem false_goal { false }",
    );
    let id = project.expect_ok("main");
    let prover = prove(&project, id, "true_goal");
    assert_eq!(prover.get_useful_fact_names(), Some(BTreeSet::new()));
    let mut prover = Prover::new(&project, false);
    assert!(prover.get_useful_fact_names().is_none());
    let node = project
        .get_env_by_id(id)
        .unwrap()
        .get_node_by_name("false_goal");
    prover.set_goal(&node.goal_context().unwrap());
    assert!(prover.get_useful_fact_names().is_none());
    assert_eq!(prover.quick_shallow_search(), Outcome::Exhausted);
    assert!(prover.get_useful_fact_names().is_none());
    assert!(prover.get_condensed_proof().is_none());
    assert!(prover.get_proof().is_none());
}

fn verify(source: &str) -> Outcome {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", source);
    let id = project.expect_ok("main");
    for node in project.get_env_by_id(id).unwrap().iter_goals() {
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
        if outcome != Outcome::Success {
            return outcome;
        }
    }
    Outcome::Success
}

#[test]
fn premise_extraction_preserves_nonempty_generated_proof_and_false_control() {
    let source = "structure Marker<T> {\n value: Bool\n}\n\
        class Marker<T> {\n define chosen(self) -> Marker<T> { axiom }\n}\n\
        let seed: Marker<Bool> = axiom\n\
        let mul: (Marker<Bool>, Marker<Bool>) -> Marker<Bool> = axiom\n\
        define marked(n: Marker<Bool>) -> Bool { exists(d: Marker<Bool>) { mul(seed, d) = n } }\n\
        axiom marker_right(a: Marker<Bool>, b: Marker<Bool>) { b = seed.chosen -> mul(a, b) = seed.chosen }\n\
        axiom unused { true }\n\
        theorem goal { marked(seed.chosen) }";
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", source);
    let id = project.expect_ok("main");
    let prover = prove(&project, id, "goal");
    let names = prover.get_useful_fact_names().unwrap();
    assert!(names.contains(&(id, "marked".into())), "{names:?}");
    assert!(names.contains(&(id, "marker_right".into())), "{names:?}");
    assert!(!names.contains(&(id, "unused".into())));
    assert!(!names.contains(&(id, "goal".into())));
    let env = project.get_env_by_id(id).unwrap();
    let code = prover
        .get_condensed_proof()
        .unwrap()
        .to_code(&env.bindings)
        .unwrap();
    assert!(!code.is_empty());
    assert_eq!(
        prover.get_proof().unwrap().to_code(&env.bindings).unwrap(),
        code
    );
    assert_eq!(prover.get_useful_fact_names().unwrap(), names);
    assert_eq!(
        verify(&format!("{source} by {{\n{}\n}}", code.join("\n"))),
        Outcome::Success
    );
    assert_eq!(
        verify(&format!(
            "{source} by {{ exists(p: Marker<Bool>) {{ p != p }} }}"
        )),
        Outcome::Exhausted
    );
}

#[test]
fn simplification_keeps_both_named_premises_for_a_completed_proof() {
    let source = r#"
            type Foo: axiom
            let foo: Foo -> Bool = axiom
            let bar: Foo = axiom
            let baz: Foo = axiom
            axiom foo_bar {
                foo(bar)
            }
            axiom foo_bar_imp_foo_baz {
                foo(bar) implies foo(baz)
            }
            theorem goal {
               foo(baz)
            }
        "#;
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", source);
    let id = project.expect_ok("main");
    let prover = prove(&project, id, "goal");
    assert_eq!(
        prover.get_useful_fact_names(),
        Some(BTreeSet::from([
            (id, "foo_bar".into()),
            (id, "foo_bar_imp_foo_baz".into()),
        ]))
    );
    assert_eq!(
        verify(&format!("{source} by {{ false }}")),
        Outcome::Exhausted
    );
}
