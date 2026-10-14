// Modified for Venticorn: structural recursion checks must reject unsafe references.
use venticorn::acorn_type::AcornType;
use venticorn::acorn_value::AcornValue;
use venticorn::termination_checker::TerminationChecker;

fn recursive() -> AcornValue {
    AcornValue::new_constant(
        10,
        "f".into(),
        AcornType::new_functional(vec![AcornType::Bool], AcornType::Bool),
        vec![],
    )
}

#[test]
fn nonrecursive_values_need_no_decreasing_argument() {
    assert!(TerminationChecker::new(10, "f".into(), 0).check(&AcornValue::Bool(true)));
}

#[test]
fn recursive_values_and_unchanged_calls_are_rejected() {
    assert!(!TerminationChecker::new(10, "f".into(), 1).check(&recursive()));
    let call = AcornValue::new_apply(recursive(), vec![AcornValue::Variable(0, AcornType::Bool)]);
    assert!(!TerminationChecker::new(10, "f".into(), 1).check(&call));
}

#[test]
fn partially_bound_recursion_checks_missing_arguments_without_panicking() {
    let f = AcornValue::new_constant(
        10,
        "f".into(),
        AcornType::new_functional(vec![AcornType::Bool, AcornType::Bool], AcornType::Bool),
        vec![],
    );
    let call = AcornValue::new_apply(f, vec![AcornValue::Variable(0, AcornType::Bool)]);
    assert!(!TerminationChecker::new(10, "f".into(), 2).check(&call));
}
