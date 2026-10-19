use venticorn::environment::Environment;
use venticorn::proof_step::Truthiness;
use venticorn::source::SourceType;

#[test]
fn class_law_propositions_retain_the_canonical_declared_formal() {
    let mut env = Environment::new_test();
    env.add("typeclass S: Singleton {\n value: S\n unique(x: S) { x = S.value }\n}");
    let class = env.bindings.get_typeclass_for_name("Singleton").unwrap();
    let info = env.bindings.get_typeclass_info(class).unwrap();
    assert_eq!(env.nodes.len(), 1);
    let prop = env.nodes[0].proposition().unwrap();
    assert_eq!(prop.params, [info.instance_param.clone()]);
    assert_eq!(prop.params[0].typeclass.as_ref(), Some(class));
    assert_eq!(prop.value, info.conditions["unique"].claim);
    assert_eq!(prop.source.range, info.conditions["unique"].range);
    assert_eq!(prop.source.module, env.module_id);
    assert_eq!(prop.source.depth, 0);
    assert!(prop.source.importable);
    assert!(
        matches!(&prop.source.source_type, SourceType::Axiom(Some(name)) if name == "Singleton.unique")
    );
    assert_eq!(prop.truthiness(), Truthiness::Factual);
    assert!(prop.has_generic());
    assert_eq!(env.iter_goals().count(), 0);
    // Recording full formals does not silently admit erased class laws.
    env.bad("typeclass T: Impossible {\n impossible { false }\n}");
    assert!(env.bindings.get_typeclass_for_name("Impossible").is_none());
    assert_eq!(env.nodes.len(), 1);
}

#[test]
fn definition_propositions_keep_ordered_phantom_formals_from_the_declaration() {
    use venticorn::acorn_type::AcornType;
    use venticorn::acorn_value::AcornValue;
    let mut env = Environment::new_test();
    env.add("typeclass M: Marked {\n flag: Bool\n}\ndefine chosen<T: Marked, U> -> Bool { true }\ndefine fixed -> Bool { true }");
    let expected = env.bindings.get_params("chosen");
    assert_eq!(expected.len(), 2);
    assert_eq!(expected[0].name, "T");
    assert_eq!(expected[1].name, "U");
    assert_eq!(
        expected[0].typeclass.as_ref(),
        env.bindings.get_typeclass_for_name("Marked")
    );
    assert!(expected[1].typeclass.is_none());
    let mut found = Vec::new();
    for node in &env.nodes {
        let Some(prop) = node.proposition() else {
            continue;
        };
        let SourceType::ConstantDefinition(value, name) = &prop.source.source_type else {
            continue;
        };
        let AcornValue::Constant(constant) = value else {
            panic!("definition identity")
        };
        assert_eq!(constant.instance_type, AcornType::Bool);
        assert_eq!(prop.source.module, env.module_id);
        assert_eq!(prop.truthiness(), Truthiness::Factual);
        if name == "chosen" {
            assert_eq!(prop.params, expected);
            assert_eq!(
                constant.params,
                expected
                    .iter()
                    .cloned()
                    .map(AcornType::Variable)
                    .collect::<Vec<_>>()
            );
            assert!(prop.has_generic());
        } else {
            assert_eq!(name, "fixed");
            assert!(prop.params.is_empty());
            assert!(constant.params.is_empty());
            assert!(!prop.has_generic());
        }
        prop.value.validate().unwrap();
        found.push(name.as_str());
    }
    assert_eq!(found, ["chosen", "fixed"]);
}
