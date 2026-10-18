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

#[test]
fn source_constructors_preserve_location_exportability_and_contextual_roles() {
    use tower_lsp::lsp_types::{Position, Range};
    use venticorn::source::SourceType;

    let range = Range::new(Position::new(4, 2), Position::new(8, 6));
    let definition = AcornValue::Bool(true);
    for (source, source_type, importable) in [
        (
            Source::theorem(true, 7, range, 3, Some("named".into())),
            SourceType::Axiom(Some("named".into())),
            true,
        ),
        (
            Source::theorem(false, 7, range, 3, None),
            SourceType::Theorem(None),
            true,
        ),
        (Source::anonymous(7, range, 3), SourceType::Anonymous, false),
        (
            Source::inhabited(7, "Item", range, 3),
            SourceType::TypeDefinition("Item".into(), "constraint".into()),
            true,
        ),
        (
            Source::type_definition(7, range, 3, "Item".into(), "member".into()),
            SourceType::TypeDefinition("Item".into(), "member".into()),
            true,
        ),
        (
            Source::constant_definition(7, range, 3, definition.clone(), "value"),
            SourceType::ConstantDefinition(definition.clone(), "value".into()),
            false,
        ),
        (
            Source::instance(7, range, 3, "Item", "Marked"),
            SourceType::Instance("Item".into(), "Marked".into()),
            true,
        ),
        (Source::premise(7, range, 3), SourceType::Premise, false),
        (
            Source::negated_goal(7, range, 3),
            SourceType::NegatedGoal,
            false,
        ),
    ] {
        assert_eq!(
            source,
            Source::new(7, range, source_type.clone(), importable, 3)
        );
        let expected = if matches!(source_type, SourceType::NegatedGoal) {
            Truthiness::Counterfactual
        } else {
            Truthiness::Hypothetical
        };
        assert_eq!(
            Proposition::new(AcornValue::Bool(true), source.clone()).truthiness(),
            expected
        );
        let proposition = Proposition::new(AcornValue::Bool(true), source.clone())
            .with_truthiness(Truthiness::Factual);
        assert_eq!(proposition.truthiness(), Truthiness::Factual);
        assert_eq!(
            proposition.with_value(AcornValue::Bool(false)).source,
            source
        );
        assert_eq!(
            proposition.with_value(AcornValue::Bool(false)).truthiness(),
            Truthiness::Factual
        );
    }
    assert!(Source::constant_definition(7, range, 0, definition.clone(), "value").importable);
    let proposition = Proposition::named_constant_definition(
        AcornValue::Bool(false),
        7,
        range,
        definition,
        "value".into(),
    )
    .with_depth(3)
    .with_truthiness(Truthiness::Factual);
    assert!(proposition.source.importable);
    let negated = proposition.with_negated_goal(AcornValue::Bool(true));
    assert_eq!(negated.source, Source::negated_goal(7, range, 3));
    assert_eq!(negated.truthiness(), Truthiness::Counterfactual);
    assert_eq!(proposition.source.depth, 3);
    assert_eq!(proposition.truthiness(), Truthiness::Factual);
}

#[test]
fn fresh_fact_and_negated_source_keep_location_and_explicit_roles() {
    use venticorn::fact::Fact;
    use venticorn::source::SourceType;
    let source = Source {
        module: 7,
        depth: 3,
        importable: true,
        ..Source::mock()
    };
    let fact = Fact::proposition(AcornValue::Bool(true), source.clone());
    assert_eq!(fact.source(), &source);
    assert_eq!(fact.truthiness(), Some(Truthiness::Hypothetical));
    let original = Proposition::new(AcornValue::Bool(true), source.clone())
        .with_truthiness(Truthiness::Factual);
    let negated = original.with_negated_goal(AcornValue::Bool(false));
    assert_eq!(negated.source, source.as_negated_goal());
    assert_eq!(negated.source.module, source.module);
    assert_eq!(negated.source.range, source.range);
    assert_eq!(negated.source.depth, source.depth);
    assert!(!negated.source.importable);
    assert!(matches!(
        negated.source.source_type,
        SourceType::NegatedGoal
    ));
    assert_eq!(negated.truthiness(), Truthiness::Counterfactual);
    assert_eq!(original.truthiness(), Truthiness::Factual);
    assert_eq!(original.source, source);
}
