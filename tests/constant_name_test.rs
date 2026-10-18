use venticorn::acorn_type::Class;
use venticorn::acorn_type::{AcornType, Typeclass};
use venticorn::binding_map::BindingMap;
use venticorn::constant_name::LocalConstantName;
use venticorn::module::FIRST_NORMAL;

#[test]
fn structured_availability_preserves_all_namespace_collisions() {
    let mut bindings = BindingMap::new(FIRST_NORMAL);
    bindings.add_data_type("Data");
    bindings.add_typeclass(
        "Class",
        Typeclass {
            module_id: FIRST_NORMAL,
            name: "Class".into(),
        },
    );
    bindings.import_module("dependency", FIRST_NORMAL + 1);
    bindings.add_constant("value", vec![], AcornType::Bool, None, None);
    for name in ["Data", "Class", "dependency", "value"] {
        assert!(bindings.typename_in_use(name), "{}", name);
        assert!(bindings.lowercase_name_in_use(name), "{}", name);
        assert!(
            bindings.constant_name_in_use(&LocalConstantName::unqualified(name)),
            "{}",
            name
        );
    }
    assert!(!bindings.typename_in_use("unused"));
    assert!(!bindings.constant_name_in_use(&LocalConstantName::unqualified("unused")));
    assert!(bindings.has_typename("Data"));
    assert!(!bindings.has_constant_name("Data"));
    assert!(bindings.has_constant_name("value"));
    assert!(!bindings.has_typename("value"));
    assert_eq!(
        bindings.get_type_for_constant_name("value"),
        Some(AcornType::Bool)
    );
    assert_eq!(
        bindings.get_type_for_identifier("value"),
        bindings.get_type_for_constant_name("value")
    );
    assert_eq!(
        bindings.get_type_for_name("Data"),
        Some(&AcornType::Data(
            Class::new(FIRST_NORMAL, "Data".into()),
            vec![]
        ))
    );
    assert!(bindings.get_type_for_typename("Data").is_some());
}

#[test]
fn constructors_retain_complete_class_and_target_identity() {
    let class = Typeclass {
        module_id: FIRST_NORMAL + 1,
        name: "Magma".into(),
    };
    assert_eq!(
        LocalConstantName::unqualified("x"),
        LocalConstantName::Unqualified("x".into())
    );
    assert_eq!(
        LocalConstantName::attribute("State", "flag"),
        LocalConstantName::Attribute("State".into(), "flag".into())
    );
    assert_eq!(
        LocalConstantName::instance(&class, "combine", "State"),
        LocalConstantName::Instance(class, "combine".into(), "State".into())
    );
}

#[test]
fn instance_names_are_qualified_but_not_data_attributes() {
    let class = Typeclass {
        module_id: FIRST_NORMAL,
        name: "Magma".into(),
    };
    assert!(!LocalConstantName::unqualified("x").is_qualified());
    let attribute = LocalConstantName::attribute("State", "flag");
    assert!(attribute.is_qualified());
    assert_eq!(attribute.as_attribute(), Some(("State", "flag")));
    let instance = LocalConstantName::instance(&class, "flag", "State");
    assert!(instance.is_qualified());
    assert_eq!(instance.as_attribute(), None);
}

#[test]
fn typed_instance_lookup_requires_its_published_canonical_scope() {
    use venticorn::environment::Environment;
    let mut env = Environment::new_test();
    env.add("typeclass T: Marked {\n flag: Bool\n}\ninductive State {\n clean\n}\ninstance State: Marked {\n let flag: Bool = true\n}");
    let class = env
        .bindings
        .get_typeclass_for_name("Marked")
        .unwrap()
        .clone();
    let good = LocalConstantName::instance(&class, "flag", "State");
    let other_class = Typeclass {
        module_id: class.module_id + 1,
        name: class.name.clone(),
    };
    let wrong = LocalConstantName::instance(&other_class, "flag", "State");
    assert_eq!(good.to_string(), wrong.to_string());
    assert_eq!(
        env.bindings.get_constant_value_named(&good),
        env.bindings.get_constant_value("State.Marked.flag")
    );
    assert!(env.bindings.get_constant_value_named(&good).is_some());
    assert!(env.bindings.get_constant_value_named(&wrong).is_none());
    env.bindings
        .add_constant("Absent.Marked.flag", vec![], AcornType::Bool, None, None);
    assert!(env
        .bindings
        .get_constant_value("Absent.Marked.flag")
        .is_some());
    assert!(env
        .bindings
        .get_constant_value_named(&LocalConstantName::instance(&class, "flag", "Absent"))
        .is_none());
    assert!(env
        .bindings
        .get_constant_value_named(&LocalConstantName::instance(&class, "missing", "State"))
        .is_none());
}

#[test]
fn checked_lookup_reports_absence_at_the_requesting_token() {
    use venticorn::token::TokenType;
    let bindings = BindingMap::new(FIRST_NORMAL);
    let token = TokenType::Identifier.new_token("missing");
    for name in [
        LocalConstantName::unqualified("missing"),
        LocalConstantName::attribute("State", "missing"),
        LocalConstantName::instance(
            &Typeclass {
                module_id: FIRST_NORMAL + 1,
                name: "Marked".into(),
            },
            "flag",
            "State",
        ),
    ] {
        assert!(bindings.get_constant_value_named(&name).is_none());
        let error = bindings.checked_constant_value(&token, &name).unwrap_err();
        assert_eq!(error.range(), token.range());
        let kind = if name.is_qualified() {
            "attribute"
        } else {
            "identifier"
        };
        assert_eq!(error.message(), format!("unknown {} '{}'", kind, name));
    }
}

#[test]
fn owned_type_lookup_preserves_pending_and_computed_alias_types() {
    use venticorn::acorn_type::TypeParam;
    use venticorn::acorn_value::AcornValue;
    use venticorn::binding_map::PotentialValue;

    let mut bindings = BindingMap::new(FIRST_NORMAL);
    let formals = vec![TypeParam {
        name: "Unused".into(),
        typeclass: Some(Typeclass {
            module_id: FIRST_NORMAL + 1,
            name: "Marked".into(),
        }),
    }];
    let pending =
        PotentialValue::constant(FIRST_NORMAL + 1, "flag", AcornType::Bool, formals.clone());
    bindings.add_alias("flag", FIRST_NORMAL + 1, "flag".into(), pending.clone());
    assert_eq!(
        bindings.get_type_for_constant_name("flag"),
        Some(AcornType::Bool)
    );
    assert_eq!(bindings.get_constant_value("flag"), Some(pending));
    assert_eq!(
        bindings
            .get_constant_value("flag")
            .unwrap()
            .unresolved_params(),
        formals
    );
    assert!(!bindings.is_constant("flag"));

    let lambda = AcornValue::lambda(
        vec![AcornType::Bool],
        AcornValue::Variable(0, AcornType::Bool),
    );
    let expected = lambda.get_type();
    bindings.add_alias(
        "identity",
        FIRST_NORMAL + 1,
        "identity".into(),
        PotentialValue::Resolved(lambda),
    );
    assert_eq!(
        bindings.get_type_for_identifier("identity"),
        Some(expected.clone())
    );
    let mut retrieved = bindings.get_type_for_constant_name("identity").unwrap();
    assert_eq!(retrieved, expected);
    retrieved = AcornType::Bool;
    assert_ne!(
        bindings.get_type_for_constant_name("identity"),
        Some(retrieved)
    );
    assert_eq!(bindings.get_type_for_constant_name("missing"), None);
}
