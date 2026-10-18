use venticorn::acorn_value::AcornValue;
use venticorn::environment::Environment;
use venticorn::proposition::SourceType;

#[test]
fn every_instance_has_a_node_without_changing_real_obligations() {
    for (law, proof, count, structural) in [
        ("", "", 0, true),
        ("", " by {\n true\n}", 2, false),
        (" law(x: T) { x = x }\n", "", 1, false),
    ] {
        let source = format!("inductive Unit {{\n only\n}}\ntypeclass T: Marked {{\n flag: Bool\n{law}}}\ninstance Unit: Marked {{\n let flag: Bool = true\n}}{proof}");
        let mut env = Environment::new_test();
        env.add(&source);
        assert_eq!(env.iter_goals().count(), count);
        let instances = env
            .nodes
            .iter()
            .filter(|node| {
                node.proposition().is_some_and(|prop| {
                    matches!(
                        &prop.source.source_type,
                        SourceType::Instance(name, class) if name == "Unit" && class == "Marked"
                    )
                })
            })
            .collect::<Vec<_>>();
        assert_eq!(instances.len(), 1);
        let node = instances[0];
        assert_eq!(node.is_structural(), structural);
        assert_eq!(node.get_block().is_none(), structural);
        assert_eq!(node.proposition().unwrap().value, AcornValue::Bool(true));
        assert_eq!(node.fact_name().as_deref(), Some("Unit.instance.Marked"));
        assert!(node.importable());
        let class = env.bindings.get_typeclass_for_name("Marked").unwrap();
        assert!(!node
            .proof_scope()
            .has_membership(env.module_id, "Unit", class));
        assert!(env
            .bindings
            .proof_scope()
            .has_membership(env.module_id, "Unit", class));
    }
}
