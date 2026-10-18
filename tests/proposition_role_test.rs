use tower_lsp::lsp_types::Range;
use venticorn::acorn_value::AcornValue;
use venticorn::fact::Fact;
use venticorn::proof_step::Truthiness;
use venticorn::proposition::Proposition;

#[test]
fn contextual_roles_survive_value_substitution_without_rewriting_sources() {
    for depth in [0, 3] {
        let original =
            Proposition::anonymous(AcornValue::Bool(true), 7, Range::default()).with_depth(depth);
        for role in [
            Truthiness::Factual,
            Truthiness::Hypothetical,
            Truthiness::Counterfactual,
        ] {
            let contextual = original.clone().with_truthiness(role);
            assert_eq!(contextual.source, original.source);
            assert_eq!(contextual.truthiness(), role);
            for transformed in [
                contextual.with_value(AcornValue::Bool(false)),
                contextual.instantiate(&[]),
            ] {
                assert_eq!(transformed.truthiness(), role);
                assert_eq!(transformed.source, original.source);
            }
            assert_eq!(contextual.clone().with_depth(9).truthiness(), role);
            let fact = Fact::new(original.clone(), role);
            assert_eq!(fact.as_proposition().unwrap().truthiness(), role);
            assert_eq!(fact.as_proposition().unwrap().source, original.source);
            let negated = contextual.with_negated_goal(AcornValue::Bool(false));
            assert_eq!(negated.truthiness(), Truthiness::Counterfactual);
            assert_eq!(negated.source.depth, depth);
            assert_eq!(negated.source.range, original.source.range);
            assert_eq!(negated.source.module, original.source.module);
            assert!(!negated.source.importable);
        }
    }
}

#[test]
fn partial_definition_substitution_preserves_role_and_unresolved_actuals() {
    use venticorn::acorn_type::{AcornType, TypeParam};
    use venticorn::proposition::{Source, SourceType};
    let t = AcornType::Variable(TypeParam::unconstrained("T"));
    let u = AcornType::Variable(TypeParam::unconstrained("U"));
    let value = AcornValue::constant(7, "flag".into(), vec![t, u.clone()], AcornType::Bool);
    let source = Source {
        source_type: SourceType::ConstantDefinition(value.clone(), "flag".into()),
        ..Source::mock()
    };
    let original = Proposition::new(value, source).with_truthiness(Truthiness::Hypothetical);
    let partial = original.instantiate(&[("T".into(), AcornType::Bool)]);
    assert!(partial.value.is_generic());
    assert_eq!(partial.truthiness(), Truthiness::Hypothetical);
    let AcornValue::Constant(constant) = &partial.value else {
        panic!("constant")
    };
    assert_eq!(constant.params, vec![AcornType::Bool, u]);
    let SourceType::ConstantDefinition(defined, name) = &partial.source.source_type else {
        panic!("definition")
    };
    assert_eq!(name, "flag");
    assert_eq!(defined, &partial.value);
    assert_eq!(partial.source.range, original.source.range);
    assert_eq!(partial.source.module, original.source.module);
    let complete = partial.instantiate(&[("U".into(), AcornType::Bool)]);
    assert!(!complete.value.is_generic());
    assert_eq!(complete.truthiness(), Truthiness::Hypothetical);
}
