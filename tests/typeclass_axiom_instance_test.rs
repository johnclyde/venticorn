use venticorn::project::Project;
use venticorn::prover::Outcome;

#[test]
fn a_typeclass_axiom_applies_to_a_declared_instance() {
    let text = r#"
            typeclass F: FooTrue {
                b: Bool
            }

            define foo<T>(t: T) -> Bool {
                axiom
            }

            axiom foo_true<F: FooTrue>(a: F) {
                foo(a)
            }

            inductive Z1 {
                zero
            }

            instance Z1: FooTrue {
                let b: Bool = true
            }

            theorem goal(z: Z1) {
                foo(z)
            }
        "#;
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", text);
    let module = project.expect_ok("main");
    let env = project.get_env_by_id(module).unwrap();
    let goals = env.iter_goals().collect::<Vec<_>>();
    assert_eq!(goals.len(), 1);
    for node in goals {
        let goal = node.goal_context().unwrap();
        let mut shallow = project.prover_for_node(&node, false);
        shallow.set_goal(&goal);
        assert_eq!(shallow.quick_shallow_search(), Outcome::Success);
        let mut ordinary = project.prover_for_node(&node, false);
        ordinary.set_goal(&goal);
        assert_eq!(ordinary.quick_search(), Outcome::Success);
        assert!(ordinary.get_proof().is_some());
    }
}
