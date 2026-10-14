// Modified for Venticorn: instantiate generic facts only for consistent proof demand.
use venticorn::acorn_type::AcornType;
use venticorn::acorn_value::AcornValue;
use venticorn::fact::Fact;
use venticorn::monomorphizer::Monomorphizer;
use venticorn::proof_step::Truthiness;
use venticorn::proposition::Source;

fn variable(name: &str) -> AcornType {
    AcornType::Variable(name.into(), None)
}
fn predicate(name: &str, actuals: Vec<AcornType>) -> AcornValue {
    let names: Vec<_> = (0..actuals.len()).map(|i| format!("P{i}")).collect();
    AcornValue::Constant(
        10,
        name.into(),
        AcornType::new_functional(names.iter().map(|n| variable(n)).collect(), AcornType::Bool),
        names.into_iter().zip(actuals).collect(),
    )
}
fn claim(name: &str, actuals: Vec<AcornType>) -> AcornValue {
    let args = actuals
        .iter()
        .enumerate()
        .map(|(i, t)| AcornValue::Variable(i as u16, t.clone()))
        .collect();
    AcornValue::new_forall(
        actuals.clone(),
        AcornValue::new_apply(predicate(name, actuals), args),
    )
}
fn fact(value: AcornValue, truthiness: Truthiness) -> Fact {
    value.validate().unwrap();
    Fact {
        value,
        source: Source::mock(),
        truthiness,
    }
}

#[test]
fn admitted_facts_and_goals_supply_demand_in_either_order() {
    for first in [true, false] {
        for truthiness in [
            Truthiness::Factual,
            Truthiness::Hypothetical,
            Truthiness::Counterfactual,
        ] {
            let mut mono = Monomorphizer::new();
            let generic = fact(claim("f", vec![variable("V")]), Truthiness::Factual);
            let concrete = claim("f", vec![AcornType::Bool]);
            if first {
                mono.add_fact(generic.clone());
                assert!(mono.take_facts().is_empty());
            }
            mono.add_fact(fact(concrete.clone(), truthiness));
            if !first {
                mono.add_fact(generic);
            }
            let output = mono.take_facts();
            assert_eq!(output.len(), 2);
            assert!(output
                .iter()
                .any(|f| f.truthiness == Truthiness::Factual && f.value == concrete));
            mono.match_constants(&concrete);
            assert!(
                mono.take_facts().is_empty(),
                "repeated demand must be deduplicated"
            );
        }
    }
    let mut mono = Monomorphizer::new();
    mono.add_fact(fact(claim("f", vec![variable("V")]), Truthiness::Factual));
    let concrete = claim("f", vec![AcornType::Bool]);
    mono.match_constants(&concrete);
    assert_eq!(
        mono.take_facts().len(),
        1,
        "explicit goal demand must instantiate the generic fact"
    );
    mono.match_constants(&concrete);
    assert!(mono.take_facts().is_empty());
}

#[test]
fn generated_instances_preserve_transitive_definition_demand() {
    let mut mono = Monomorphizer::new();
    let t = variable("V");
    mono.add_fact(fact(
        AcornValue::new_and(claim("f", vec![t.clone()]), claim("g", vec![t])),
        Truthiness::Factual,
    ));
    mono.add_fact(fact(claim("g", vec![variable("W")]), Truthiness::Factual));
    mono.match_constants(&predicate("f", vec![AcornType::Bool]));
    assert_eq!(mono.take_facts().len(), 2);
    mono.match_constants(&predicate("g", vec![AcornType::Bool]));
    assert!(
        mono.take_facts().is_empty(),
        "transitive instances must be deduplicated"
    );
}

#[test]
fn conflicting_repeated_parameters_do_not_create_or_cache_an_instance() {
    let mut mono = Monomorphizer::new();
    mono.add_fact(fact(
        claim("f", vec![variable("V"), variable("V")]),
        Truthiness::Factual,
    ));
    mono.match_constants(&predicate(
        "f",
        vec![AcornType::Bool, AcornType::Data(10, "Nat".into())],
    ));
    assert!(mono.take_facts().is_empty());
    mono.match_constants(&predicate("f", vec![AcornType::Bool, AcornType::Bool]));
    let output = mono.take_facts();
    assert_eq!(output.len(), 1);
    output[0].value.validate().unwrap();
    assert!(!output[0].value.is_generic());
}

#[test]
fn incomplete_fact_substitutions_wait_without_panicking_or_emitting() {
    let mut mono = Monomorphizer::new();
    let value = AcornValue::new_and(
        claim("f", vec![variable("V")]),
        claim("g", vec![variable("W")]),
    );
    mono.add_fact(fact(value, Truthiness::Factual));
    mono.match_constants(&predicate("f", vec![AcornType::Bool]));
    assert!(mono.take_facts().is_empty());
}
