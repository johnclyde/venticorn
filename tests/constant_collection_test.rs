// Modified for Venticorn: inspect complete instances throughout expression traversal.
use venticorn::acorn_type::AcornType;
use venticorn::acorn_value::AcornValue;

fn generic(name: &str) -> AcornValue {
    let t = AcornType::Variable("T".into(), None);
    AcornValue::new_constant(10, name.into(), vec![t.clone()], t)
}
fn names(value: &AcornValue, generic_only: bool) -> Vec<String> {
    let mut found = vec![];
    value.find_constants(&|c| !generic_only || c.is_generic(), &mut found);
    found.into_iter().map(|c| c.name).collect()
}

#[test]
fn collection_visits_function_arguments_binders_conditions_and_match_branches() {
    // Traversal is structural; isolated patterns do not need constructor admission.
    let application = AcornValue::new_apply(
        AcornValue::new_constant(
            10,
            "function".into(),
            vec![],
            AcornType::new_functional(vec![AcornType::Bool], AcornType::Bool),
        ),
        vec![generic("argument")],
    );
    let matched = AcornValue::Match(
        Box::new(generic("scrutinee")),
        vec![(vec![], generic("pattern"), generic("result"))],
    );
    let expression = AcornValue::new_forall(
        vec![AcornType::Bool],
        AcornValue::IfThenElse(
            Box::new(application),
            Box::new(AcornValue::Not(Box::new(generic("negated")))),
            Box::new(matched),
        ),
    );
    assert_eq!(
        names(&expression, false),
        [
            "function",
            "argument",
            "negated",
            "scrutinee",
            "pattern",
            "result"
        ]
    );
    assert_eq!(
        names(&expression, true),
        ["argument", "negated", "scrutinee", "pattern", "result"]
    );
    let mut found = vec![];
    generic("identity").find_constants(&|_| true, &mut found);
    assert_eq!(found[0].key().module, 10);
    assert_eq!(found[0].key().name, "identity");
    assert_eq!(AcornValue::Constant(found.remove(0)), generic("identity"));
}

#[test]
fn plain_scoped_types_are_generic_even_without_type_arguments() {
    let plain = AcornValue::new_constant(
        10,
        "local".into(),
        vec![],
        AcornType::Variable("T".into(), None),
    );
    assert_eq!(names(&plain, true), ["local"]);
    assert!(names(&plain.to_arbitrary(), true).is_empty());
}
