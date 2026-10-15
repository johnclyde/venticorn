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
    let instance_type = AcornType::new_functional(actuals.clone(), AcornType::Bool);
    AcornValue::new_constant(10, name.into(), actuals, instance_type)
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
            mono.add_monomorphs(&concrete);
            assert!(
                mono.take_facts().is_empty(),
                "repeated demand must be deduplicated"
            );
        }
    }
    let mut mono = Monomorphizer::new();
    mono.add_fact(fact(claim("f", vec![variable("V")]), Truthiness::Factual));
    let concrete = claim("f", vec![AcornType::Bool]);
    mono.add_monomorphs(&concrete);
    assert_eq!(
        mono.take_facts().len(),
        1,
        "explicit goal demand must instantiate the generic fact"
    );
    mono.add_monomorphs(&concrete);
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
    mono.add_monomorphs(&predicate("f", vec![AcornType::Bool]));
    assert_eq!(mono.take_facts().len(), 2);
    mono.add_monomorphs(&predicate("g", vec![AcornType::Bool]));
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
    mono.add_monomorphs(&predicate(
        "f",
        vec![AcornType::Bool, AcornType::Data(10, "Nat".into(), vec![])],
    ));
    assert!(mono.take_facts().is_empty());
    mono.add_monomorphs(&predicate("f", vec![AcornType::Bool, AcornType::Bool]));
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
    mono.add_monomorphs(&predicate("f", vec![AcornType::Bool]));
    assert!(mono.take_facts().is_empty());
}

#[test]
fn constant_matching_uses_declared_positions_and_rejects_wrong_arity() {
    let mut mono = Monomorphizer::new();
    mono.add_fact(fact(
        claim("ordered", vec![variable("B"), variable("A")]),
        Truthiness::Factual,
    ));
    // An inconsistent request cannot truncate a zip or contaminate later requests.
    mono.add_monomorphs(&predicate("ordered", vec![AcornType::Bool]));
    assert!(mono.take_facts().is_empty());
    let nat = AcornType::Data(10, "Nat".into(), vec![]);
    mono.add_monomorphs(&predicate("ordered", vec![nat.clone(), AcornType::Bool]));
    let emitted = mono.take_facts();
    assert_eq!(emitted.len(), 1);
    assert_eq!(
        emitted[0].value,
        claim("ordered", vec![nat, AcornType::Bool])
    );
}
