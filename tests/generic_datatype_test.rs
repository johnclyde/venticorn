use std::collections::HashMap;
use venticorn::acorn_type::AcornType;
use venticorn::acorn_type::Class;

fn data(name: &str, args: Vec<AcornType>) -> AcornType {
    AcornType::Data(Class::new(10, name.into()), args)
}

#[test]
fn datatype_arguments_preserve_identity_and_recursive_type_operations() {
    let variable = AcornType::Variable(venticorn::acorn_type::TypeParam {
        name: "T".into(),
        typeclass: None,
    });
    let nested = data("Outer", vec![data("Inner", vec![variable.clone()])]);
    assert!(nested.is_generic());
    assert!(nested.has_type_variable("T"));
    assert!(!nested.is_normalized());
    assert!(nested.refers_to(10, "Inner"));
    let concrete = data("Outer", vec![data("Inner", vec![AcornType::Bool])]);
    assert_eq!(
        nested.instantiate(&[("T".into(), AcornType::Bool)]),
        concrete
    );
    let mut mapping = HashMap::new();
    assert!(nested.match_instance(&concrete, &mut mapping));
    assert_eq!(mapping.get("T"), Some(&AcornType::Bool));
    assert!(!nested.match_instance(
        &AcornType::Data(Class::new(11, "Outer".into()), vec![AcornType::Bool]),
        &mut HashMap::new()
    ));
    assert!(!nested.match_instance(&data("Outer", vec![]), &mut HashMap::new()));
    assert!(nested.to_arbitrary().is_normalized());
    let pair = data("Pair", vec![AcornType::Bool, data("Nat", vec![])]);
    assert_ne!(
        pair,
        data("Pair", vec![data("Nat", vec![]), AcornType::Bool])
    );
    assert_eq!(pair.to_string(), "Pair<Bool, Nat>");
    assert_eq!(
        data(
            "Wrap",
            vec![AcornType::Arbitrary(venticorn::acorn_type::TypeParam {
                name: "T".into(),
                typeclass: None
            })]
        )
        .parametrize(10, &["T".into()]),
        data("Wrap", vec![variable])
    );
}

#[test]
fn parameterized_numerals_reject_without_erasing_actuals() {
    let mut env = venticorn::environment::Environment::new_test();
    env.bindings
        .add_type_alias("Specialized", data("Family", vec![AcornType::Bool]));
    env.bad("numerals Specialized");
    let hidden = data(
        "Hidden",
        vec![AcornType::Variable(venticorn::acorn_type::TypeParam {
            name: "T".into(),
            typeclass: None,
        })],
    );
    let value = venticorn::acorn_value::AcornValue::Variable(0, hidden);
    assert!(venticorn::normalizer::Normalizer::new()
        .term_from_value(&value, false)
        .is_err());
}

#[test]
fn pending_type_declarations_require_their_exact_arity() {
    use venticorn::binding_map::BindingMap;
    use venticorn::module::FIRST_NORMAL;
    let mut bindings = BindingMap::new(FIRST_NORMAL);
    bindings.add_potential_type("Pair", 2);
    bindings.add_data_type("Nat");
    bindings.assert_type_ok("Pair<Bool, Nat>");
    bindings.assert_type_ok("Pair<Nat, Bool>");
    bindings.assert_type_ok("Pair<Pair<Bool, Nat>, (Bool -> Bool) -> Bool>");
    bindings.assert_type_bad("Pair");
    bindings.assert_type_bad("Pair<Bool>");
    bindings.assert_type_bad("Pair<Bool, Bool, Bool>");
    bindings.assert_type_bad("Bool<Bool>");
    bindings.assert_type_bad("Pair(Bool, Bool)");
}

#[test]
fn generic_type_names_can_resolve_canonical_member_heads() {
    use venticorn::acorn_type::AcornType;
    use venticorn::environment::Environment;
    let mut env = Environment::new_test();
    env.bindings.add_potential_type("Family", 1);
    env.bindings.add_constant(
        "Family.value",
        vec![venticorn::acorn_type::TypeParam::unconstrained("T")],
        AcornType::Variable(venticorn::acorn_type::TypeParam {
            name: "T".into(),
            typeclass: None,
        }),
        None,
        None,
    );
    env.add("let value: Bool = Family.value<Bool>");
    env.bad("let bad: Bool = Family.missing<Bool>");
    assert!(!env.bindings.has_identifier("bad"));
}

#[test]
fn specialized_type_alias_members_never_discard_fixed_arguments() {
    use venticorn::environment::Environment;
    let mut env = Environment::new_test();
    env.bindings.add_potential_type("Box", 1);
    let generic = AcornType::Variable(venticorn::acorn_type::TypeParam {
        name: "T".into(),
        typeclass: None,
    });
    env.bindings.add_constant(
        "Box.new",
        vec![venticorn::acorn_type::TypeParam::unconstrained("T")],
        AcornType::new_functional(
            vec![generic.clone()],
            AcornType::Data(Class::new(env.module_id, "Box".into()), vec![generic]),
        ),
        None,
        None,
    );
    env.bindings.add_type_alias(
        "BoolBox",
        AcornType::Data(
            Class::new(env.module_id, "Box".into()),
            vec![AcornType::Bool],
        ),
    );
    env.add("let okay: Box<Bool> = Box.new(true)");
    env.add("let alias: Box<Bool> = BoolBox.new(true)");
    env.add("type Item: axiom\nlet item: Item = axiom");
    env.bad("let bad: Box<Item> = BoolBox.new(item)");
    env.bad("let bad: Box<Item> = BoolBox.new<Item>(item)");
    assert!(!env.bindings.has_identifier("bad"));
}

#[test]
fn arbitrary_type_detection_visits_effective_and_binder_metadata() {
    use venticorn::acorn_value::{AcornValue, ConstantInstance};
    let arbitrary = AcornType::Arbitrary(venticorn::acorn_type::TypeParam {
        name: "T".into(),
        typeclass: None,
    });
    let wrapped = data("Wrap", vec![arbitrary.clone()]);
    let constant = AcornValue::Constant(ConstantInstance {
        name: venticorn::constant_name::GlobalConstantName::new(
            10,
            venticorn::constant_name::LocalConstantName::unqualified("hidden"),
        ),
        params: vec![],
        instance_type: wrapped.clone(),
    });
    assert!(constant.has_arbitrary());
    assert!(
        AcornValue::ForAll(vec![wrapped.clone()], Box::new(AcornValue::Bool(true))).has_arbitrary()
    );
    assert!(AcornValue::Match(
        Box::new(AcornValue::Bool(true)),
        vec![(
            vec![wrapped],
            AcornValue::Bool(true),
            AcornValue::Bool(true)
        )]
    )
    .has_arbitrary());
    assert_eq!(
        data("Wrap", vec![arbitrary]).to_generic(),
        data(
            "Wrap",
            vec![AcornType::Variable(venticorn::acorn_type::TypeParam {
                name: "T".into(),
                typeclass: None
            })]
        )
    );
}

#[test]
fn generic_theorem_signatures_reject_outer_captures_before_binding() {
    use venticorn::environment::Environment;
    use venticorn::project::Project;
    use venticorn::statement::Statement;
    for inner in [
        "theorem inner<T>(x: A) { true }",
        "theorem<T>(x: A) { true }",
        "define inner<T>(x: A) -> Bool { true }",
    ] {
        let mut env = Environment::new_test();
        let text = format!("theorem outer<A> {{ true }} by {{\n {inner}\n}}");
        let statement = Statement::parse_str(&text).unwrap();
        let error = env
            .add_statement(&mut Project::new_mock(), &statement)
            .unwrap_err();
        assert!(
            error
                .to_string()
                .contains("cannot capture outer arbitrary types"),
            "{error}"
        );
        assert!(!env.bindings.has_identifier("outer"));
        assert!(!env.bindings.has_identifier("inner"));
        assert!(!env.bindings.has_type_name("A"));
        assert!(!env.bindings.has_type_name("T"));
        assert!(env.nodes.is_empty());
    }
    let mut env = Environment::new_test();
    env.add("theorem outer<A> { true } by {\n theorem inner(x: A) { x = x }\n define identity(x: A) -> A { x }\n}");
}

#[test]
fn typed_application_checks_both_resolved_and_pending_heads() {
    use venticorn::acorn_value::AcornValue;
    use venticorn::binding_map::{BindingMap, PotentialValue};
    use venticorn::module::FIRST_NORMAL;
    use venticorn::token::TokenType;
    let mut bindings = BindingMap::new(FIRST_NORMAL);
    let token = TokenType::Identifier.new_token("call");
    let ordinary = AcornValue::new_constant(
        FIRST_NORMAL,
        "plain".into(),
        vec![],
        AcornType::new_functional(vec![AcornType::Bool], AcornType::Bool),
    );
    assert!(bindings
        .apply_potential(
            &token,
            PotentialValue::Resolved(ordinary.clone()),
            vec![AcornValue::Bool(true)],
            Some(&AcornType::Bool)
        )
        .is_ok());
    assert!(bindings
        .apply_potential(
            &token,
            PotentialValue::Resolved(ordinary.clone()),
            vec![AcornValue::Bool(true), AcornValue::Bool(true)],
            None
        )
        .is_err());
    assert!(bindings
        .apply_potential(
            &token,
            PotentialValue::Resolved(ordinary),
            vec![AcornValue::Variable(0, data("Nat", vec![]))],
            None
        )
        .is_err());
    let t = AcornType::Variable(venticorn::acorn_type::TypeParam {
        name: "T".into(),
        typeclass: None,
    });
    bindings.add_constant(
        "id",
        vec![venticorn::acorn_type::TypeParam::unconstrained("T")],
        AcornType::new_functional(vec![t.clone()], t),
        None,
        None,
    );
    for args in [vec![], vec![AcornValue::Bool(true), AcornValue::Bool(true)]] {
        assert!(bindings
            .apply_potential(
                &token,
                bindings.get_constant_value("id").unwrap(),
                args,
                None
            )
            .is_err());
    }
    assert!(bindings
        .apply_potential(
            &token,
            bindings.get_constant_value("id").unwrap(),
            vec![AcornValue::Bool(true)],
            Some(&data("Nat", vec![]))
        )
        .is_err());
}

#[test]
fn arbitrary_conversion_preserves_effective_types_and_unused_binders() {
    use venticorn::acorn_value::AcornValue;
    let arbitrary = data(
        "Wrap",
        vec![AcornType::Arbitrary(venticorn::acorn_type::TypeParam {
            name: "T".into(),
            typeclass: None,
        })],
    );
    for value in [
        AcornValue::new_constant(10, "hidden".into(), vec![], arbitrary.clone()),
        AcornValue::new_constant(
            10,
            "phantom".into(),
            vec![arbitrary.clone()],
            AcornType::Bool,
        ),
        AcornValue::Lambda(vec![arbitrary.clone()], Box::new(AcornValue::Bool(true))),
        AcornValue::ForAll(vec![arbitrary.clone()], Box::new(AcornValue::Bool(true))),
        AcornValue::Exists(vec![arbitrary.clone()], Box::new(AcornValue::Bool(true))),
        AcornValue::Match(
            Box::new(AcornValue::Bool(true)),
            vec![(
                vec![arbitrary],
                AcornValue::Bool(true),
                AcornValue::Bool(true),
            )],
        ),
    ] {
        let generic = value.to_generic();
        if let AcornValue::Constant(instance) = &value {
            assert_eq!(generic, AcornValue::Constant(instance.to_generic()));
        }
        assert!(!generic.has_arbitrary(), "{value:?}");
        assert!(generic.has_generic(), "{value:?}");
        assert_eq!(generic.to_arbitrary(), value);
    }
}
