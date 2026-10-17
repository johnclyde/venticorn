use venticorn::acorn_type::AcornType;
use venticorn::acorn_value::{AcornValue, FunctionApplication};
use venticorn::normalizer::{Normalization, Normalizer};

#[test]
fn direct_normalization_rejects_malformed_applications_before_reading_their_type() {
    let malformed = AcornValue::Application(FunctionApplication {
        function: Box::new(AcornValue::Bool(true)),
        args: vec![AcornValue::Bool(false)],
    });
    let expected = format!(
        "validation error: {} while normalizing: {}",
        malformed.validate().unwrap_err(),
        malformed
    );
    match Normalizer::new().normalize(&malformed, false) {
        Normalization::Error(error) => assert_eq!(error, expected),
        result => panic!("malformed application was normalized: {result:?}"),
    }
}

#[test]
fn direct_normalization_reports_non_boolean_values_without_panicking() {
    let value = AcornValue::constant(
        2,
        "item".into(),
        vec![],
        AcornType::Data(2, "Item".into(), vec![]),
    );
    value.validate().unwrap();
    match Normalizer::new().normalize(&value, false) {
        Normalization::Error(error) => {
            assert_eq!(error, "normalization requires a Boolean value, got Item")
        }
        result => panic!("non-Boolean value was normalized: {result:?}"),
    }
}

#[test]
fn term_normalization_returns_the_original_diagnostic_as_a_string() {
    let error: String = Normalizer::new()
        .term_from_value(&AcornValue::Bool(false), false)
        .unwrap_err();
    assert_eq!(error, "Cannot convert false to term");
}

#[test]
fn structured_skolem_names_keep_their_exact_rejection_diagnostic() {
    use venticorn::constant_name::{GlobalConstantName, LocalConstantName};
    use venticorn::module::SKOLEM;

    let value = AcornValue::constant_named(
        GlobalConstantName::new(SKOLEM, LocalConstantName::attribute("Type", "member")),
        vec![],
        AcornType::Bool,
    );
    let error: String = Normalizer::new()
        .term_from_value(&value, false)
        .unwrap_err();
    assert_eq!(error, "invalid structured skolem name");
}
