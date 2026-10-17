use venticorn::acorn_type::{AcornType, Typeclass};
use venticorn::acorn_value::AcornValue;
use venticorn::constant_name::{GlobalConstantName, LocalConstantName};
use venticorn::termination_checker::TerminationChecker;

fn instance(owner: u16) -> GlobalConstantName {
    GlobalConstantName::new(
        10,
        LocalConstantName::instance(
            &Typeclass {
                module_id: owner,
                name: "Marked".into(),
            },
            "step",
            "State",
        ),
    )
}

#[test]
fn typed_termination_targets_preserve_canonical_class_identity() {
    let name = instance(11);
    let value = AcornValue::constant_named(
        name.clone(),
        vec![],
        AcornType::new_functional(vec![AcornType::Bool], AcornType::Bool),
    );
    let call = AcornValue::apply(
        value.clone(),
        vec![AcornValue::Variable(0, AcornType::Bool)],
    );
    let mut same = TerminationChecker::new_named(name.clone(), 1);
    assert!(!same.check(&call));
    assert!(same.is_recursive());
    assert!(!TerminationChecker::new_named(name, 1).check(&value));
    let mut foreign = TerminationChecker::new_named(instance(12), 1);
    assert!(foreign.check(&call));
    assert!(!foreign.is_recursive());
    assert!(!TerminationChecker::new(10, "State.Marked.step".into(), 1).check(&call));
}

#[test]
fn raw_simple_names_retain_compatibility_without_guessing_instance_owners() {
    let attribute = GlobalConstantName::new(10, LocalConstantName::attribute("State", "step"));
    let value = AcornValue::constant_named(attribute.clone(), vec![], AcornType::Bool);
    assert!(!TerminationChecker::new_named(attribute, 0).check(&value));
    assert!(!TerminationChecker::new(10, "State.step".into(), 0).check(&value));
    assert!(TerminationChecker::new(10, "different".into(), 0).check(&value));
    assert!(TerminationChecker::new_named(instance(11), 0).check(&AcornValue::Bool(true)));
}
