// Modified for Venticorn: exercise match binders without enabling incomplete proof lowering.
use venticorn::acorn_type::AcornType;
use venticorn::acorn_value::{AcornValue, BinaryOp};
use venticorn::binding_map::BindingMap;
use venticorn::module::FIRST_NORMAL;
use venticorn::normalizer::{Normalization, Normalizer};

fn bound_match(acorn_type: AcornType) -> AcornValue {
    AcornValue::Match(
        Box::new(AcornValue::Variable(0, acorn_type.clone())),
        vec![(
            vec![acorn_type.clone()],
            AcornValue::Variable(1, acorn_type.clone()),
            AcornValue::Variable(1, acorn_type),
        )],
    )
}

#[test]
fn match_case_binders_follow_type_transformations() {
    let concrete = AcornType::Data(FIRST_NORMAL, "T".to_string());
    let value = bound_match(concrete);
    let parameterized = value.parametrize(FIRST_NORMAL, &["T".to_string()]);
    let AcornValue::Match(_, cases) = &parameterized else {
        panic!("expected a match")
    };
    assert_eq!(cases[0].0, vec![AcornType::Variable("T".to_string(), None)]);
    let specialized = parameterized.instantiate(&[("T".to_string(), AcornType::Bool)]);
    assert_eq!(specialized, bound_match(AcornType::Bool));
    let placeholder = parameterized.to_arbitrary();
    assert_eq!(
        placeholder,
        bound_match(AcornType::Arbitrary("T".to_string(), None))
    );
}

#[test]
fn substituting_outer_values_preserves_match_case_scope() {
    let substituted = bound_match(AcornType::Bool).bind_values(0, 0, &[AcornValue::Bool(true)]);
    assert_eq!(
        substituted,
        AcornValue::Match(
            Box::new(AcornValue::Bool(true)),
            vec![(
                vec![AcornType::Bool],
                AcornValue::Variable(0, AcornType::Bool),
                AcornValue::Variable(0, AcornType::Bool)
            )],
        )
    );
    substituted.validate().unwrap();
    let inserted = bound_match(AcornType::Bool).insert_stack(0, 1);
    let AcornValue::Match(scrutinee, cases) = inserted else {
        panic!("expected a match")
    };
    assert_eq!(*scrutinee, AcornValue::Variable(1, AcornType::Bool));
    assert_eq!(cases[0].1, AcornValue::Variable(2, AcornType::Bool));
}

#[test]
fn match_normalization_completes_while_codegen_reports_unsupported() {
    let value = bound_match(AcornType::Bool).bind_values(0, 0, &[AcornValue::Bool(true)]);
    let boolean = AcornValue::Binary(
        BinaryOp::Equals,
        Box::new(AcornValue::Bool(false)),
        Box::new(value.clone()),
    );
    let nested = AcornValue::Not(Box::new(AcornValue::new_forall(vec![], boolean)));
    for expression in [value.clone(), nested] {
        let result = Normalizer::new().normalize(&expression, false);
        assert!(!matches!(result, Normalization::Error(_)), "{result:?}");
    }
    assert!(BindingMap::new(FIRST_NORMAL).value_to_code(&value).is_err());
}

#[test]
fn malformed_matches_fail_normalization_before_type_access() {
    let empty = AcornValue::Match(Box::new(AcornValue::Bool(true)), vec![]);
    for value in [
        empty.clone(),
        AcornValue::new_equals(AcornValue::Bool(false), empty),
    ] {
        assert!(matches!(Normalizer::new().normalize(&value, false),
            Normalization::Error(message) if message.contains("at least one case")));
    }
}

#[test]
fn match_lowering_checks_nested_boolean_scopes_without_panicking() {
    let value = bound_match(AcornType::Bool).bind_values(0, 0, &[AcornValue::Bool(true)]);
    let expressions = [
        AcornValue::new_and(AcornValue::Bool(true), value.clone()),
        AcornValue::new_forall(vec![AcornType::Bool], value.clone().insert_stack(0, 1)),
        AcornValue::new_exists(vec![AcornType::Bool], value.insert_stack(0, 1).negate()),
    ];
    for expression in expressions {
        expression.validate().unwrap();
        let lowered = expression.replace_match(0).unwrap();
        assert!(!lowered.contains_match());
        lowered.validate().unwrap();
    }
    let plain = AcornValue::new_and(AcornValue::Bool(true), AcornValue::Bool(false));
    assert_eq!(plain.clone().replace_match(0).unwrap(), plain);
}
