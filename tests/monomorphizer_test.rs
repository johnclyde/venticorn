use venticorn::acorn_type::Class;
// Modified for Venticorn: instantiate generic facts only for consistent proof demand.
use venticorn::acorn_type::AcornType;
use venticorn::acorn_value::AcornValue;
use venticorn::fact::Fact;
use venticorn::monomorphizer::Monomorphizer;
use venticorn::proof_step::Truthiness;
use venticorn::proposition::Source;

fn variable(name: &str) -> AcornType {
    AcornType::Variable(venticorn::acorn_type::TypeParam {
        name: name.into(),
        typeclass: None,
    })
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
    Fact::new(
        venticorn::proposition::Proposition::new(value, Source::mock()),
        truthiness,
    )
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
                .any(|f| f.truthiness() == Some(Truthiness::Factual)
                    && f.as_proposition().unwrap().value == concrete));
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
        vec![
            AcornType::Bool,
            AcornType::Data(Class::new(10, "Nat".into()), vec![]),
        ],
    ));
    assert!(mono.take_facts().is_empty());
    mono.add_monomorphs(&predicate("f", vec![AcornType::Bool, AcornType::Bool]));
    let output = mono.take_facts();
    assert_eq!(output.len(), 1);
    output[0]
        .as_proposition()
        .unwrap()
        .value
        .validate()
        .unwrap();
    assert!(!output[0].as_proposition().unwrap().value.is_generic());
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
    let nat = AcornType::Data(Class::new(10, "Nat".into()), vec![]);
    mono.add_monomorphs(&predicate("ordered", vec![nat.clone(), AcornType::Bool]));
    let emitted = mono.take_facts();
    assert_eq!(emitted.len(), 1);
    assert_eq!(
        emitted[0].as_proposition().unwrap().value,
        claim("ordered", vec![nat, AcornType::Bool])
    );
}

#[test]
fn whole_fact_bounds_guard_phantom_actuals_before_substitution() {
    use venticorn::acorn_type::{TypeParam, Typeclass};
    let class = Typeclass {
        module_id: 10,
        name: "Magma".into(),
    };
    let bound = AcornType::Variable(TypeParam {
        name: "T".into(),
        typeclass: Some(class.clone()),
    });
    let loose = variable("T");
    let constant = |name: &str, actual: AcornType| {
        AcornValue::new_constant(10, name.into(), vec![actual], AcornType::Bool)
    };
    let mut mono = Monomorphizer::new();
    mono.add_fact(fact(
        AcornValue::new_and(constant("loose", loose), constant("bound", bound)),
        Truthiness::Factual,
    ));
    for actual in [
        AcornType::Bool,
        AcornType::Arbitrary(TypeParam::unconstrained("U")),
        AcornType::Arbitrary(TypeParam {
            name: "U".into(),
            typeclass: Some(Typeclass {
                module_id: 11,
                name: "Magma".into(),
            }),
        }),
    ] {
        mono.add_monomorphs(&constant("loose", actual.clone()));
        mono.add_monomorphs(&constant("bound", actual));
        assert!(mono.take_facts().is_empty());
    }
    let valid = AcornType::Arbitrary(TypeParam {
        name: "U".into(),
        typeclass: Some(class),
    });
    mono.add_monomorphs(&constant("loose", valid.clone()));
    let output = mono.take_facts();
    assert_eq!(
        output.len(),
        1,
        "failed requests must not poison a later valid request"
    );
    assert_eq!(
        output[0].as_proposition().unwrap().value,
        AcornValue::new_and(constant("loose", valid.clone()), constant("bound", valid))
    );
}

#[test]
fn bounds_in_binders_and_effective_types_are_checked_for_whole_fact_demand() {
    use venticorn::acorn_type::{TypeParam, Typeclass};
    let class = Typeclass {
        module_id: 10,
        name: "Magma".into(),
    };
    let bound = AcornType::Variable(TypeParam {
        name: "T".into(),
        typeclass: Some(class.clone()),
    });
    let nested = AcornType::Data(
        Class::new(10, "Wrap".into()),
        vec![AcornType::new_functional(vec![bound.clone()], bound)],
    );
    let seed = |actual| AcornValue::new_constant(10, "seed".into(), vec![actual], AcornType::Bool);
    let mut mono = Monomorphizer::new();
    let value = AcornValue::Variable(0, nested.clone());
    let generic = AcornValue::new_and(
        seed(variable("T")),
        AcornValue::new_forall(vec![nested], AcornValue::new_equals(value.clone(), value)),
    );
    mono.add_fact(fact(generic.clone(), Truthiness::Factual));
    mono.add_monomorphs(&seed(AcornType::Bool));
    assert!(mono.take_facts().is_empty());
    let valid = AcornType::Arbitrary(TypeParam {
        name: "U".into(),
        typeclass: Some(class),
    });
    mono.add_monomorphs(&seed(valid.clone()));
    let output = mono.take_facts();
    assert_eq!(output.len(), 1);
    assert_eq!(
        output[0].as_proposition().unwrap().value,
        generic.instantiate(&[("T".into(), valid)])
    );
}

#[test]
fn generic_no_demand_facts_are_not_emitted_from_nested_binders() {
    use venticorn::acorn_type::{TypeParam, Typeclass};
    let param = TypeParam {
        name: "T".into(),
        typeclass: Some(Typeclass {
            module_id: 10,
            name: "Magma".into(),
        }),
    };
    for value in [
        AcornValue::new_exists(
            vec![AcornType::Variable(param.clone())],
            AcornValue::Bool(false),
        ),
        AcornValue::Not(Box::new(AcornValue::new_exists(
            vec![AcornType::Variable(param.clone())],
            AcornValue::Bool(true),
        ))),
    ] {
        let mut mono = Monomorphizer::new();
        mono.add_fact(fact(value, Truthiness::Factual));
        assert!(mono.take_facts().is_empty());
    }
    let mut mono = Monomorphizer::new();
    mono.add_fact(fact(
        AcornValue::new_exists(vec![AcornType::Arbitrary(param)], AcornValue::Bool(true)),
        Truthiness::Factual,
    ));
    assert_eq!(
        mono.take_facts().len(),
        1,
        "fixed scoped types remain usable"
    );
}

#[test]
fn concrete_scope_checks_whole_fact_bounds_before_phantom_erasure() {
    use venticorn::acorn_type::TypeParam;
    use venticorn::project::Project;
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", "typeclass T: Marked {\n flag: Bool\n}\ntype Item: axiom\ninstance Item: Marked {\n let flag: Bool = true\n}");
    let id = project.expect_ok("main");
    let bindings = &project.get_env_by_id(id).unwrap().bindings;
    let bound = AcornType::Variable(TypeParam {
        name: "T".into(),
        typeclass: Some(bindings.get_typeclass_for_name("Marked").unwrap().clone()),
    });
    let constant = |name: &str, actual: AcornType| {
        AcornValue::new_constant(id, name.into(), vec![actual], AcornType::Bool)
    };
    let generic = AcornValue::new_and(constant("loose", variable("T")), constant("bound", bound));
    let mut mono = Monomorphizer::with_scope(bindings.proof_scope().clone());
    mono.add_fact(fact(generic.clone(), Truthiness::Factual));
    for actual in [
        AcornType::Bool,
        AcornType::Data(Class::new(id + 1, "Item".into()), vec![]),
        AcornType::Data(Class::new(id, "Item".into()), vec![AcornType::Bool]),
    ] {
        mono.add_monomorphs(&constant("loose", actual));
        assert!(mono.take_facts().is_empty());
    }
    let valid = AcornType::Data(Class::new(id, "Item".into()), vec![]);
    mono.add_monomorphs(&constant("loose", valid.clone()));
    let output = mono.take_facts();
    assert_eq!(output.len(), 1);
    assert_eq!(
        output[0].as_proposition().unwrap().value,
        generic.instantiate(&[("T".into(), valid)])
    );
}
