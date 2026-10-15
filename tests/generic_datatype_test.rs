use std::collections::HashMap;
use venticorn::acorn_type::AcornType;

fn data(name: &str, args: Vec<AcornType>) -> AcornType {
    AcornType::Data(10, name.into(), args)
}

#[test]
fn datatype_arguments_preserve_identity_and_recursive_type_operations() {
    let variable = AcornType::Variable("T".into(), None);
    let nested = data("Outer", vec![data("Inner", vec![variable.clone()])]);
    assert!(nested.is_generic());
    assert!(nested.has_type_variable("T"));
    assert!(!nested.is_normalized());
    assert!(nested.refers_to(10, "Inner"));
    let concrete = data("Outer", vec![data("Inner", vec![AcornType::Bool])]);
    assert_eq!(
        nested.instantiate(&[("T".into(), AcornType::Bool)]),
        concrete
    );
    let mut mapping = HashMap::new();
    assert!(nested.match_instance(&concrete, &mut mapping));
    assert_eq!(mapping.get("T"), Some(&AcornType::Bool));
    assert!(!nested.match_instance(
        &AcornType::Data(11, "Outer".into(), vec![AcornType::Bool]),
        &mut HashMap::new()
    ));
    assert!(!nested.match_instance(&data("Outer", vec![]), &mut HashMap::new()));
    assert!(nested.to_arbitrary().is_normalized());
    let pair = data("Pair", vec![AcornType::Bool, data("Nat", vec![])]);
    assert_ne!(
        pair,
        data("Pair", vec![data("Nat", vec![]), AcornType::Bool])
    );
    assert_eq!(pair.to_string(), "Pair<Bool, Nat>");
    assert_eq!(
        data("Wrap", vec![AcornType::Arbitrary("T".into(), None)]).parametrize(10, &["T".into()]),
        data("Wrap", vec![variable])
    );
}

#[test]
fn parameterized_numerals_reject_without_erasing_actuals() {
    let mut env = venticorn::environment::Environment::new_test();
    env.bindings
        .add_type_alias("Specialized", data("Family", vec![AcornType::Bool]));
    env.bad("numerals Specialized");
    let hidden = data("Hidden", vec![AcornType::Variable("T".into(), None)]);
    let value = venticorn::acorn_value::AcornValue::Variable(0, hidden);
    assert!(venticorn::normalizer::Normalizer::new()
        .term_from_value(&value, false)
        .is_err());
}
