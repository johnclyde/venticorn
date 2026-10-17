use venticorn::acorn_type::{AcornType, Typeclass};
use venticorn::acorn_value::AcornValue;
use venticorn::constant_name::{GlobalConstantName, LocalConstantName};

fn instance(owner: u16) -> GlobalConstantName {
    GlobalConstantName::new(
        10,
        LocalConstantName::instance(
            &Typeclass {
                module_id: owner,
                name: "Marked".into(),
            },
            "flag",
            "State",
        ),
    )
}

#[test]
fn borrowed_accessors_keep_canonical_owners_and_complete_actuals() {
    let name = instance(11);
    let value = AcornValue::constant_named(name.clone(), vec![], AcornType::Bool);
    let AcornValue::Constant(constant) = &value else {
        panic!("expected constant")
    };
    assert!(std::ptr::eq(value.constant_name().unwrap(), &constant.name));
    assert!(std::ptr::eq(
        value.simple_constant_name().unwrap(),
        &constant.name
    ));
    assert_eq!(value.constant_name(), Some(&name));
    assert_ne!(value.constant_name(), Some(&instance(12)));
    assert_eq!(value.as_name(), Some((10, "State.Marked.flag".into())));
    assert_eq!(value.as_simple_constant(), value.as_name());

    let specialized =
        AcornValue::constant_named(name.clone(), vec![AcornType::Bool], AcornType::Bool);
    assert_eq!(specialized.constant_name(), Some(&name));
    assert!(specialized.simple_constant_name().is_none());
    assert!(specialized.as_simple_constant().is_none());
    assert!(AcornValue::Bool(true).constant_name().is_none());
    assert!(AcornValue::Bool(true).simple_constant_name().is_none());
}

#[test]
fn named_function_access_is_borrowed_and_does_not_describe_other_values() {
    let name = instance(11);
    let function = AcornValue::constant_named(
        name.clone(),
        vec![],
        AcornType::new_functional(vec![AcornType::Bool], AcornType::Bool),
    );
    assert!(function.named_function_name().is_none());
    let call = AcornValue::apply(function, vec![AcornValue::Bool(true)]);
    let AcornValue::Application(application) = &call else {
        panic!("expected application")
    };
    assert!(std::ptr::eq(
        call.named_function_name().unwrap(),
        application.function.constant_name().unwrap()
    ));
    assert_eq!(call.named_function_name(), Some(&name));
    assert_eq!(
        call.is_named_function_call(),
        Some((10, "State.Marked.flag".into()))
    );
    assert!(call.constant_name().is_none());
    let lambda = AcornValue::Lambda(
        vec![AcornType::Bool],
        Box::new(AcornValue::Variable(0, AcornType::Bool)),
    );
    let lambda_call = AcornValue::apply(lambda, vec![AcornValue::Bool(true)]);
    assert!(lambda_call.named_function_name().is_none());
    assert!(lambda_call.is_named_function_call().is_none());
}
