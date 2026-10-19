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
