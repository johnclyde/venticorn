use venticorn::acorn_type::{AcornType, TypeParam, Typeclass};
use venticorn::acorn_value::AcornValue;
use venticorn::proof_step::Truthiness;
use venticorn::proposition::Proposition;
use venticorn::source::Source;

#[test]
fn parameter_lists_show_bounds_without_using_display_as_identity() {
    let bounded = TypeParam {
        name: "Z".into(),
        typeclass: Some(Typeclass {
            module_id: 7,
            name: "Marked".into(),
        }),
    };
    let foreign = TypeParam {
        name: "Z".into(),
        typeclass: Some(Typeclass {
            module_id: 8,
            name: "Marked".into(),
        }),
    };
    let unbounded = TypeParam::unconstrained("A");
    assert_eq!(bounded.to_string(), "Z: Marked");
    assert_eq!(unbounded.to_string(), "A");
    assert_eq!(bounded.to_string(), foreign.to_string());
    assert_ne!(bounded, foreign);
    assert_eq!(TypeParam::params_to_str(&[]), "<>");
    assert_eq!(
        TypeParam::params_to_str(&[bounded.clone(), unbounded.clone()]),
        "<Z: Marked, A>"
    );
    assert_eq!(AcornType::Variable(bounded.clone()).to_string(), "Z");
    assert_eq!(AcornType::Arbitrary(bounded.clone()).to_string(), "Z");
    assert_eq!(
        AcornType::types_to_str(&[AcornType::Variable(bounded), AcornType::Variable(unbounded)]),
        "Z, A"
    );
}

#[test]
fn proposition_display_includes_phantom_formals_without_changing_metadata() {
    let params = vec![TypeParam {
        name: "T".into(),
        typeclass: Some(Typeclass {
            module_id: 9,
            name: "Marked".into(),
        }),
    }];
    let source = Source::mock();
    let proposition = Proposition::generic(AcornValue::Bool(true), params.clone(), source.clone())
        .with_truthiness(Truthiness::Counterfactual);
    assert_eq!(proposition.to_string(), "<T: Marked> true");
    assert_eq!(proposition.params, params);
    assert_eq!(proposition.source, source);
    assert_eq!(proposition.truthiness(), Truthiness::Counterfactual);
    assert_eq!(proposition.value, AcornValue::Bool(true));
    let fixed = Proposition::new(AcornValue::Bool(false), Source::mock());
    assert_eq!(fixed.to_string(), "false");
    assert_eq!(fixed.into_monomorphic().unwrap().to_string(), "false");
}
