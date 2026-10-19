use venticorn::environment::Environment;
use venticorn::proof_step::Truthiness;
use venticorn::source::SourceType;

#[test]
fn structure_equations_keep_ordered_phantom_bounds_and_source_metadata() {
    let mut env = Environment::new_test();
    env.add("typeclass M: Magma {\n mul: (M, M) -> M\n}\ntypeclass O: Other {\n item: O\n}\nstructure Phantom<T: Magma, U: Other> {\n flag: Bool\n}\nstructure Fixed {\n flag: Bool\n}");
    let formals = env.bindings.get_params("Phantom.new");
    assert_eq!(formals.len(), 2);
    assert_eq!(formals[0].name, "T");
    assert_eq!(formals[1].name, "U");
    assert_eq!(
        formals[0].typeclass.as_ref(),
        env.bindings.get_typeclass_for_name("Magma")
    );
    assert_eq!(
        formals[1].typeclass.as_ref(),
        env.bindings.get_typeclass_for_name("Other")
    );
    let mut found = Vec::new();
    for node in &env.nodes {
        let Some(prop) = node.proposition() else {
            continue;
        };
        let SourceType::TypeDefinition(name, member) = &prop.source.source_type else {
            continue;
        };
        if name != "Phantom" && name != "Fixed" {
            continue;
        }
        assert!(member == "new" || member == "flag");
        prop.value.validate().unwrap();
        assert_eq!(prop.source.module, env.module_id);
        assert_eq!(prop.source.depth, 0);
        assert!(prop.source.importable);
        assert_eq!(prop.truthiness(), Truthiness::Factual);
        if name == "Phantom" {
            assert_eq!(prop.params, formals);
            assert!(prop.has_generic());
        } else {
            assert!(prop.params.is_empty());
            assert!(!prop.has_generic());
        }
        found.push((name.as_str(), member.as_str()));
    }
    assert_eq!(
        found,
        [
            ("Phantom", "new"),
            ("Phantom", "flag"),
            ("Fixed", "new"),
            ("Fixed", "flag")
        ]
    );
}

#[test]
fn structure_constraint_equations_keep_full_formals_and_real_existence_goal() {
    let mut env = Environment::new_test();
    env.add("typeclass M: Magma {\n mul: (M, M) -> M\n}\nstructure Flagged<T: Magma, U> {\n flag: Bool\n} constraint { flag }");
    let constraint = env
        .nodes
        .iter()
        .find_map(|node| {
            node.proposition().filter(|prop| {
                matches!(&prop.source.source_type,
            SourceType::TypeDefinition(name, member) if name == "Flagged" && member == "constraint")
            })
        })
        .unwrap();
    assert_eq!(constraint.params, env.bindings.get_params("Flagged.new"));
    assert_eq!(constraint.params.len(), 2);
    assert_eq!(constraint.params[0].name, "T");
    assert_eq!(constraint.params[1].name, "U");
    assert_eq!(
        constraint.params[0].typeclass.as_ref(),
        env.bindings.get_typeclass_for_name("Magma")
    );
    assert!(constraint.params[1].typeclass.is_none());
    assert!(constraint.has_generic());
    assert_eq!(constraint.truthiness(), Truthiness::Factual);
    assert!(constraint.source.importable);
    let goals = env.iter_goals().collect::<Vec<_>>();
    assert_eq!(goals.len(), 1);
    assert!(goals[0].current().proposition().is_none());
    let context = goals[0].goal_context().unwrap();
    assert!(!context.goal.has_generic());
    assert!(matches!(
        context.goal.value(),
        venticorn::acorn_value::AcornValue::Exists(..)
    ));
}
