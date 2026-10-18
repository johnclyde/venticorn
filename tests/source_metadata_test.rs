use venticorn::acorn_value::AcornValue;
use venticorn::proof_step::Truthiness;
use venticorn::proposition::{Proposition, Source};

#[test]
fn proposition_display_formats_only_the_value() {
    for value in [AcornValue::Bool(true), AcornValue::Bool(false)] {
        let proposition = Proposition::new(value.clone(), Source::mock())
            .with_depth(3)
            .with_truthiness(Truthiness::Counterfactual);
        assert_eq!(proposition.to_string(), value.to_string());
        assert_eq!(proposition.source.depth, 3);
        assert_eq!(proposition.truthiness(), Truthiness::Counterfactual);
    }
}

#[test]
fn source_names_keep_stable_instance_and_member_identities() {
    use venticorn::source::SourceType;

    for (source_type, expected) in [
        (
            SourceType::Instance("Item".into(), "Marked".into()),
            Some("Item.instance.Marked"),
        ),
        (
            SourceType::TypeDefinition("Item".into(), "instance.Marked.flag".into()),
            Some("Item.instance.Marked.flag"),
        ),
        (SourceType::Premise, None),
        (SourceType::NegatedGoal, None),
    ] {
        let source = Source {
            module: 7,
            source_type,
            ..Source::mock()
        };
        assert_eq!(source.name().as_deref(), expected);
        assert_eq!(
            source.qualified_name(),
            expected.map(|name| (7, name.to_string()))
        );
        assert_eq!(source.fact_name(), source.name());
        assert_eq!(source.qualified_fact_name(), source.qualified_name());
    }
}
