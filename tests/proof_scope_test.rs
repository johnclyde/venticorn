use venticorn::acorn_type::Typeclass;
use venticorn::project::Project;

const DEP: &str = "typeclass T: Marked {\n flag: Bool\n}\ntype Item: axiom\ninstance Item: Marked {\n let flag: Bool = true\n}";

#[test]
fn every_goal_keeps_its_lexical_memberships_and_import_frontier() {
    let mut project = Project::new_mock();
    project.mock("/mock/dep.ac", DEP);
    project.mock(
        "/mock/main.ac",
        "theorem before { true }\nimport dep\ntheorem after { true }",
    );
    let main = project.expect_ok("main");
    let dep = project.expect_ok("dep");
    let env = project.get_env_by_id(main).unwrap();
    let before = env.get_node_by_name("before").goal_context().unwrap();
    let after = env.get_node_by_name("after").goal_context().unwrap();
    let class = Typeclass {
        module_id: dep,
        name: "Marked".into(),
    };
    assert!(before.proof_scope.imports().is_empty());
    assert!(!before.proof_scope.has_membership(dep, "Item", &class));
    assert_eq!(after.proof_scope.imports(), [dep]);
    assert!(after.proof_scope.has_membership(dep, "Item", &class));
    assert!(!after.proof_scope.has_membership(main, "Item", &class));
    assert!(!after.proof_scope.has_membership(
        dep,
        "Item",
        &Typeclass {
            module_id: main,
            name: "Marked".into()
        }
    ));
}

#[test]
fn scoped_imports_affect_later_children_and_parent_but_not_earlier_children() {
    let mut project = Project::new_mock();
    project.mock("/mock/dep.ac", DEP);
    project.mock(
        "/mock/main.ac",
        "theorem outer { true } by {\n true\n import dep\n true\n}\ntheorem tail { true }",
    );
    let main = project.expect_ok("main");
    let dep = project.expect_ok("dep");
    let env = project.get_env_by_id(main).unwrap();
    let goals = env
        .iter_goals()
        .map(|n| n.goal_context().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(goals.len(), 4);
    assert!(goals[0].proof_scope.imports().is_empty());
    assert_eq!(goals[1].proof_scope.imports(), [dep]);
    assert_eq!(goals[2].proof_scope.imports(), [dep]);
    assert!(goals[3].proof_scope.imports().is_empty());
    let outer = env.get_node_by_name("outer");
    assert!(outer.current().proof_scope().imports().is_empty());
    assert!(outer
        .current()
        .block
        .as_ref()
        .unwrap()
        .entry_scope()
        .imports()
        .is_empty());
}

#[test]
fn later_local_instances_do_not_rewrite_prior_goal_metadata() {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", "typeclass T: Marked {\n flag: Bool\n}\ntype Item: axiom\ntheorem before { true }\ninstance Item: Marked {\n let flag: Bool = true\n}\ntheorem after { true }");
    let main = project.expect_ok("main");
    let env = project.get_env_by_id(main).unwrap();
    let class = Typeclass {
        module_id: main,
        name: "Marked".into(),
    };
    assert!(!env
        .get_node_by_name("before")
        .goal_context()
        .unwrap()
        .proof_scope
        .has_membership(main, "Item", &class));
    assert!(env
        .get_node_by_name("after")
        .goal_context()
        .unwrap()
        .proof_scope
        .has_membership(main, "Item", &class));
    // The registry is staged metadata at this checkpoint, not an unchecked bound resolver.
    let expression = venticorn::expression::Expression::expect_value("Marked.flag<Item>");
    assert!(env
        .bindings
        .evaluate_value(&project, &expression, None)
        .is_err());
}
