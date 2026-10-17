use venticorn::acorn_type::{AcornType, Typeclass};
use venticorn::binding_map::BindingMap;
use venticorn::constant_name::LocalConstantName;
use venticorn::module::FIRST_NORMAL;

#[test]
fn structured_availability_preserves_all_namespace_collisions() {
    let mut bindings = BindingMap::new(FIRST_NORMAL);
    bindings.add_data_type("Data");
    bindings.add_typeclass(
        "Class",
        Typeclass {
            module_id: FIRST_NORMAL,
            name: "Class".into(),
        },
    );
    bindings.import_module("dependency", FIRST_NORMAL + 1);
    bindings.add_constant("value", vec![], AcornType::Bool, None, None);
    for name in ["Data", "Class", "dependency", "value"] {
        assert!(bindings.typename_in_use(name), "{}", name);
        assert!(bindings.lowercase_name_in_use(name), "{}", name);
        assert!(
            bindings.constant_name_in_use(&LocalConstantName::Unqualified(name.into())),
            "{}",
            name
        );
    }
    assert!(!bindings.typename_in_use("unused"));
    assert!(!bindings.constant_name_in_use(&LocalConstantName::Unqualified("unused".into())));
    assert!(bindings.has_typename("Data"));
    assert!(!bindings.has_constant_name("Data"));
    assert!(bindings.has_constant_name("value"));
    assert!(!bindings.has_typename("value"));
    assert_eq!(
        bindings.get_type_for_constant_name("value"),
        Some(&AcornType::Bool)
    );
    assert_eq!(
        bindings.get_type_for_identifier("value"),
        bindings.get_type_for_constant_name("value")
    );
    assert_eq!(
        bindings.get_type_for_name("Data"),
        Some(&AcornType::Data(FIRST_NORMAL, "Data".into(), vec![]))
    );
    assert!(bindings.get_type_for_typename("Data").is_some());
}
