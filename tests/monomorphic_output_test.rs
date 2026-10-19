use venticorn::acorn_type::{AcornType, TypeParam};
use venticorn::acorn_value::AcornValue;
use venticorn::fact::Fact;
use venticorn::monomorphizer::Monomorphizer;
use venticorn::normalizer::Normalizer;
use venticorn::proof_step::Truthiness;
use venticorn::proposition::Proposition;
use venticorn::source::{Source, SourceType};

#[test]
fn fixed_output_conversion_rejects_every_unresolved_metadata_channel() {
    let formal = TypeParam::unconstrained("T");
    let generic_value = AcornValue::constant(
        7,
        "flag".into(),
        vec![AcornType::Variable(formal.clone())],
        AcornType::Bool,
    );
    let source = Source::mock();
    let inputs = [
        Proposition::generic(AcornValue::Bool(false), vec![formal], source.clone()),
        Proposition::new(generic_value.clone(), source.clone()),
        Proposition::new(
            AcornValue::Bool(false),
            Source {
                source_type: SourceType::ConstantDefinition(generic_value, "flag".into()),
                ..source
            },
        ),
    ];
    for input in inputs {
        let input = input.with_truthiness(Truthiness::Counterfactual);
        assert!(input.as_monomorphic().is_none());
        let rejected = input.clone().into_monomorphic().unwrap_err();
        assert_eq!(rejected.value, input.value);
        assert_eq!(rejected.params, input.params);
        assert_eq!(rejected.source, input.source);
        assert_eq!(rejected.truthiness(), Truthiness::Counterfactual);
        let mut mono = Monomorphizer::new();
        mono.add_fact(Fact::Proposition(input));
        assert!(mono.take_monomorphic().is_empty());
        let error = Normalizer::new()
            .normalize_monomorphic_fact(Fact::Proposition(rejected))
            .unwrap_err();
        assert_eq!(error, "cannot normalize unresolved proposition metadata");
    }
}

#[test]
fn checked_output_preserves_contextual_roles_and_revalidates_recovered_values() {
    for role in [
        Truthiness::Factual,
        Truthiness::Hypothetical,
        Truthiness::Counterfactual,
    ] {
        let input = Proposition::new(
            AcornValue::Bool(false),
            Source {
                depth: 4,
                ..Source::mock()
            },
        )
        .with_truthiness(role);
        let borrowed = input.as_monomorphic().unwrap();
        assert_eq!(borrowed.value(), &input.value);
        assert_eq!(borrowed.source(), &input.source);
        assert_eq!(borrowed.truthiness(), role);
        let mut mono = Monomorphizer::new();
        mono.add_fact(Fact::Proposition(input.clone()));
        let output = mono.take_monomorphic();
        assert_eq!(output.len(), 1);
        assert_eq!(output[0].value(), &input.value);
        assert_eq!(output[0].source(), &input.source);
        assert_eq!(output[0].truthiness(), role);
        let mut normalizer = Normalizer::new();
        let mut steps = Vec::new();
        normalizer
            .normalize_fact(Fact::Proposition(input.clone()), &mut steps)
            .unwrap();
        assert_eq!(steps.len(), 1);
        assert!(steps[0].clause.is_impossible());
        assert_eq!(steps[0].truthiness, role);
        let mut recovered = output.into_iter().next().unwrap().into_proposition();
        recovered.params.push(TypeParam::unconstrained("Phantom"));
        assert!(recovered.into_monomorphic().is_err());
    }
}
