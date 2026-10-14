// Modified for Venticorn: check concrete types across generic instantiation boundaries.
use venticorn::acorn_type::AcornType;
use venticorn::acorn_value::AcornValue;

fn variable(name: &str) -> AcornType {
    AcornType::Variable(name.into(), None)
}

fn first(params: Vec<(String, AcornType)>) -> AcornValue {
    AcornValue::new_constant(
        10,
        "first".into(),
        AcornType::new_functional(vec![variable("T"), variable("U")], variable("T")),
        params,
    )
}

#[test]
fn nested_instantiation_distinguishes_definition_and_outer_type_names() {
    let nat = AcornType::Data(10, "Nat".into());
    // The declaration's T/U are bound to the surrounding U/T respectively.
    let swapped = first(vec![
        ("T".into(), variable("U")),
        ("U".into(), variable("T")),
    ]);
    let concrete = swapped.instantiate(&[("T".into(), AcornType::Bool), ("U".into(), nat.clone())]);
    let direct = first(vec![
        ("T".into(), nat.clone()),
        ("U".into(), AcornType::Bool),
    ]);
    assert_eq!(concrete, direct);
    let nat_value = AcornValue::new_constant(10, "zero".into(), nat.clone(), vec![]);
    let application = AcornValue::new_apply(concrete, vec![nat_value, AcornValue::Bool(true)]);
    application.validate().unwrap();
    assert_eq!(application.get_type(), nat);
}

#[test]
fn repeated_actual_types_retain_both_parameter_positions() {
    let repeated = first(vec![
        ("T".into(), variable("V")),
        ("U".into(), variable("V")),
    ]);
    let concrete = repeated.instantiate(&[("V".into(), AcornType::Bool)]);
    assert_eq!(
        concrete,
        first(vec![
            ("T".into(), AcornType::Bool),
            ("U".into(), AcornType::Bool)
        ])
    );
    let application = AcornValue::new_apply(
        concrete,
        vec![AcornValue::Bool(true), AcornValue::Bool(false)],
    );
    application.validate().unwrap();
    assert_eq!(application.get_type(), AcornType::Bool);
}

#[test]
fn scoped_plain_constants_follow_the_surrounding_type_substitution() {
    let local = AcornValue::new_constant(10, "local".into(), variable("T"), vec![]);
    let concrete = local.instantiate(&[("T".into(), AcornType::Bool)]);
    concrete.validate().unwrap();
    assert_eq!(concrete.get_type(), AcornType::Bool);
    assert!(!concrete.is_generic());
    let arbitrary = local.to_arbitrary();
    assert_eq!(arbitrary.get_type(), AcornType::Arbitrary("T".into(), None));
    assert!(!arbitrary.is_generic());
}
