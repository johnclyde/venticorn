use venticorn::acorn_type::{AcornType, Class, Typeclass};
use venticorn::acorn_value::AcornValue;
use venticorn::names::{GlobalName, LocalName};

#[test]
fn explicit_instance_specialization_preserves_both_canonical_owners() {
    let class = Typeclass {
        module_id: 3,
        name: "Marked".into(),
    };
    let target = Class::new(5, "State".into());
    let value = AcornValue::instance_constant(
        class.clone(),
        "flag".into(),
        target.clone(),
        AcornType::Bool,
    );
    let AcornValue::Constant(instance) = &value else {
        panic!("expected constant")
    };
    assert_eq!(
        instance.name,
        GlobalName::new(3, LocalName::attribute("Marked", "flag"))
    );
    assert_eq!(instance.params, [AcornType::Data(target.clone(), vec![])]);
    assert_eq!(instance.instance_type, AcornType::Bool);
    assert_ne!(
        value,
        AcornValue::instance_constant(
            Typeclass {
                module_id: 4,
                ..class.clone()
            },
            "flag".into(),
            target.clone(),
            AcornType::Bool
        )
    );
    assert_ne!(
        value,
        AcornValue::instance_constant(
            class.clone(),
            "flag".into(),
            Class::new(6, "State".into()),
            AcornType::Bool
        )
    );
    assert_ne!(
        value,
        AcornValue::constant_named(
            GlobalName::new(5, LocalName::instance(&class, "flag", "State")),
            vec![],
            AcornType::Bool
        )
    );
}
