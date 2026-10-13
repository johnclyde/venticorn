// Modified for Venticorn: validate application types before admitting logical facts.
use venticorn::acorn_type::AcornType;
use venticorn::acorn_value::AcornValue;

fn identity(t: AcornType) -> AcornValue {
    AcornValue::Constant(
        10,
        "identity".into(),
        AcornType::new_functional(vec![t.clone()], t),
        vec![],
    )
}

#[test]
fn malformed_applications_fail_validation_without_panicking() {
    let nat = AcornType::Data(10, "Nat".into());
    for value in [
        AcornValue::new_apply(AcornValue::Bool(true), vec![AcornValue::Bool(false)]),
        AcornValue::new_apply(identity(nat), vec![AcornValue::Bool(false)]),
        AcornValue::new_apply(
            identity(AcornType::Bool),
            vec![AcornValue::Bool(false), AcornValue::Bool(true)],
        ),
        AcornValue::new_apply(
            AcornValue::new_apply(AcornValue::Bool(true), vec![AcornValue::Bool(false)]),
            vec![AcornValue::Bool(true)],
        ),
    ] {
        assert!(value.validate().is_err());
    }
    assert!(
        AcornValue::new_apply(identity(AcornType::Bool), vec![AcornValue::Bool(false)])
            .validate()
            .is_ok()
    );
}

#[test]
fn parametrization_updates_recursive_constant_types() {
    let specific = identity(AcornType::Data(10, "T".into()));
    let generic = specific.parametrize(10, &["T".into()]);
    assert_eq!(
        generic.get_type(),
        AcornType::new_functional(
            vec![AcornType::Parameter("T".into())],
            AcornType::Parameter("T".into())
        )
    );
}

#[test]
fn constant_types_specialize_symmetrically_with_parametrization() {
    let specific = identity(AcornType::Data(10, "T".into()));
    let generic = specific.parametrize(10, &["T".into()]);
    let concrete = generic.specialize(&[("T".into(), AcornType::Bool)]);
    assert_eq!(concrete.get_type(), identity(AcornType::Bool).get_type());
    assert!(!concrete.is_parametric());
    assert!(
        AcornValue::new_apply(concrete, vec![AcornValue::Bool(true)])
            .validate()
            .is_ok()
    );
}
