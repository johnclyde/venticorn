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
