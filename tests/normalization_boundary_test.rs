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
