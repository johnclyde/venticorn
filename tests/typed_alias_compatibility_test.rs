use venticorn::acorn_type::AcornType;
use venticorn::binding_map::BindingMap;
use venticorn::constant_name::{GlobalConstantName, LocalConstantName};
use venticorn::module::FIRST_NORMAL;
use venticorn::potential_value::PotentialValue;

#[test]
fn raw_two_part_alias_preserves_attribute_lookup_without_instance_authority() {
    let mut bindings = BindingMap::new(FIRST_NORMAL);
    let canonical = GlobalConstantName::new(
        FIRST_NORMAL + 1,
        LocalConstantName::attribute("Original", "flag"),
    );
    let value = PotentialValue::constant_named(canonical, AcornType::Bool, vec![]);
    bindings.add_alias(
        "Local.flag",
        FIRST_NORMAL + 1,
        "Original.flag".into(),
        value.clone(),
    );
    assert_eq!(
        bindings.get_constant_value("Local.flag"),
        Some(value.clone())
    );
    assert_eq!(
        bindings.get_constant_value_named(&LocalConstantName::attribute("Local", "flag")),
        Some(value.clone())
    );
    bindings.add_alias(
        "State.Marked.flag",
        FIRST_NORMAL + 1,
        "Original.flag".into(),
        value,
    );
    assert!(bindings
        .get_constant_value_named(&LocalConstantName::attribute("State.Marked", "flag"))
        .is_none());
}

#[test]
fn raw_external_attribute_alias_is_the_preferred_rendering_without_a_module_import() {
    let mut bindings = BindingMap::new(FIRST_NORMAL);
    let canonical = GlobalConstantName::new(
        FIRST_NORMAL + 1,
        LocalConstantName::attribute("Pair", "new"),
    );
    let value = venticorn::acorn_value::AcornValue::constant_named(
        canonical,
        vec![],
        AcornType::functional(vec![AcornType::Bool], AcornType::Bool),
    );
    bindings.add_alias(
        "make",
        FIRST_NORMAL + 1,
        "Pair.new".into(),
        PotentialValue::Resolved(value.clone()),
    );
    assert_eq!(bindings.value_to_code(&value).unwrap(), "make");
    let opaque = venticorn::acorn_value::AcornValue::constant_named(
        GlobalConstantName::new(
            FIRST_NORMAL + 1,
            LocalConstantName::unqualified("State.Marked.flag"),
        ),
        vec![],
        AcornType::Bool,
    );
    bindings.add_alias(
        "opaque",
        FIRST_NORMAL + 1,
        "State.Marked.flag".into(),
        PotentialValue::Resolved(opaque.clone()),
    );
    assert!(bindings.value_to_code(&opaque).is_err());
}
