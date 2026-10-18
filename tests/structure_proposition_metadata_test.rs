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
