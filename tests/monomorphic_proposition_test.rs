use venticorn::acorn_type::{AcornType, TypeParam};
use venticorn::acorn_value::AcornValue;
use venticorn::fact::Fact;
use venticorn::proof_step::Truthiness;
use venticorn::proposition::Proposition;
use venticorn::source::{Source, SourceType};

#[test]
fn checked_fixed_constructor_rejects_generic_value_and_definition_metadata() {
    let variable = AcornType::Variable(TypeParam::unconstrained("T"));
    let value = AcornValue::constant(7, "flag".into(), vec![variable], AcornType::Bool);
    let source = Source::mock();
    assert_eq!(
        Proposition::monomorphic(value.clone(), source.clone()).unwrap_err(),
        "monomorphic proposition contains unresolved generic metadata"
    );
    let definition_source = Source {
        source_type: SourceType::ConstantDefinition(value.clone(), "flag".into()),
        ..source.clone()
    };
    assert_eq!(
        Proposition::monomorphic(AcornValue::Bool(true), definition_source).unwrap_err(),
        "monomorphic proposition contains unresolved generic metadata"
    );
    // Compatibility constructors continue to represent pending generic facts.
    assert!(Proposition::new(value.clone(), source.clone()).has_generic());
    assert!(Fact::proposition(value, source)
        .as_proposition()
        .unwrap()
        .has_generic());
}

#[test]
fn checked_fixed_constructor_preserves_fixed_arbitrary_types_and_proof_roles() {
    let fixed = AcornType::Arbitrary(TypeParam::unconstrained("T"));
    let value = AcornValue::constant(7, "flag".into(), vec![fixed], AcornType::Bool);
    let source = Source {
        depth: 3,
        ..Source::mock()
    };
    let proposition = Proposition::monomorphic(value.clone(), source.clone()).unwrap();
    assert_eq!(proposition.value, value);
    assert_eq!(proposition.source, source);
    assert!(proposition.params.is_empty());
    assert!(!proposition.has_generic());
    assert_eq!(proposition.truthiness(), Truthiness::Hypothetical);
    let contextual = proposition.with_truthiness(Truthiness::Counterfactual);
    assert_eq!(contextual.source, source);
    assert_eq!(contextual.truthiness(), Truthiness::Counterfactual);
}
