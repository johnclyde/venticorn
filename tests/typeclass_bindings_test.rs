use venticorn::acorn_type::Typeclass;
use venticorn::binding_map::BindingMap;

#[test]
fn class_names_preserve_canonical_identity_and_first_alias() {
    let mut bindings = BindingMap::new(2);
    let first = Typeclass {
        module_id: 2,
        name: "Magma".into(),
    };
    let foreign = Typeclass {
        module_id: 3,
        name: "Magma".into(),
    };
    bindings.add_typeclass("Magma", first.clone());
    bindings.add_typeclass("Alias", first.clone());
    bindings.add_typeclass("Foreign", foreign.clone());
    assert_eq!(bindings.get_typeclass_for_name("Magma"), Some(&first));
    assert_eq!(bindings.get_typeclass_for_name("Alias"), Some(&first));
    assert_eq!(bindings.get_typeclass_for_name("Foreign"), Some(&foreign));
    assert_ne!(first, foreign);
    assert_eq!(bindings.get_name_for_typeclass(&first), Some("Magma"));
    assert_eq!(bindings.get_name_for_typeclass(&foreign), Some("Foreign"));
    for name in ["Magma", "Alias", "Foreign"] {
        assert!(bindings.name_in_use(name));
        assert!(!bindings.has_type_name(name));
        assert!(!bindings.has_identifier(name));
    }
    let clone = bindings.clone();
    assert_eq!(clone.get_typeclass_for_name("Alias"), Some(&first));
    assert_eq!(clone.get_name_for_typeclass(&first), Some("Magma"));
}
