use venticorn::acorn_type::Typeclass;
use venticorn::binding_map::BindingMap;

#[test]
fn class_names_preserve_canonical_identity_and_first_alias() {
    let mut bindings = BindingMap::new(2);
    let first = Typeclass {
        module_id: 2,
        name: "Magma".into(),
    };
    let foreign = Typeclass {
        module_id: 3,
        name: "Magma".into(),
    };
    bindings.add_typeclass("Magma", first.clone());
    bindings.add_typeclass("Alias", first.clone());
    bindings.add_typeclass("Foreign", foreign.clone());
    assert_eq!(bindings.get_typeclass_for_name("Magma"), Some(&first));
    assert_eq!(bindings.get_typeclass_for_name("Alias"), Some(&first));
    assert_eq!(bindings.get_typeclass_for_name("Foreign"), Some(&foreign));
    assert_ne!(first, foreign);
    assert_eq!(bindings.get_name_for_typeclass(&first), Some("Magma"));
    assert_eq!(bindings.get_name_for_typeclass(&foreign), Some("Foreign"));
    for name in ["Magma", "Alias", "Foreign"] {
        assert!(bindings.name_in_use(name));
        assert!(!bindings.has_type_name(name));
        assert!(!bindings.has_identifier(name));
    }
    let clone = bindings.clone();
    assert_eq!(clone.get_typeclass_for_name("Alias"), Some(&first));
    assert_eq!(clone.get_name_for_typeclass(&first), Some("Magma"));
}

#[test]
fn datatype_declarations_reject_reserved_class_names_without_mutation() {
    use venticorn::environment::Environment;
    use venticorn::project::Project;
    use venticorn::statement::Statement;

    for source in [
        "structure Magma {\n value: Bool\n}",
        "structure Wrapper<Magma> {\n value: Magma\n}",
        "inductive Magma {\n unit\n}",
    ] {
        let mut env = Environment::new_test();
        env.add("let keep: Bool = true");
        let class = Typeclass {
            module_id: env.module_id,
            name: "Magma".into(),
        };
        env.bindings.add_typeclass("Magma", class.clone());
        let nodes = env.nodes.len();
        let last_line = env.last_line();
        let statement = Statement::parse_str(source).unwrap();
        let error = env
            .add_statement(&mut Project::new_mock(), &statement)
            .unwrap_err();
        assert!(error.message().contains("already defined"), "{error}");
        assert_eq!(env.nodes.len(), nodes);
        assert_eq!(env.last_line(), last_line);
        assert_eq!(env.bindings.get_typeclass_for_name("Magma"), Some(&class));
        assert!(!env.bindings.has_type_name("Magma"));
        assert!(!env.bindings.name_in_use("Wrapper"));
        assert!(env.bindings.has_identifier("keep"));
        env.add("structure Wrapper<T> {\n value: T\n}");
    }
}

#[test]
fn scoped_instance_types_preserve_the_canonical_class_bound() {
    use venticorn::acorn_type::AcornType;
    let class = Typeclass {
        module_id: 2,
        name: "Magma".into(),
    };
    let foreign = Typeclass {
        module_id: 3,
        name: "Magma".into(),
    };
    let mut bindings = BindingMap::new(2);
    let instance = bindings.add_arbitrary_type_with_class("M", Some(&class));
    assert_eq!(
        instance,
        AcornType::Arbitrary(venticorn::acorn_type::TypeParam {
            name: "M".into(),
            typeclass: Some(class.clone())
        })
    );
    assert_eq!(
        instance.to_generic(),
        AcornType::Variable(venticorn::acorn_type::TypeParam {
            name: "M".into(),
            typeclass: Some(class.clone())
        })
    );
    assert_eq!(
        instance.parametrize(2, &["M".into()]),
        instance.to_generic()
    );
    assert_ne!(
        instance.to_generic(),
        AcornType::Variable(venticorn::acorn_type::TypeParam {
            name: "M".into(),
            typeclass: Some(foreign)
        })
    );
    assert_eq!(
        bindings.add_arbitrary_type("U"),
        AcornType::Arbitrary(venticorn::acorn_type::TypeParam {
            name: "U".into(),
            typeclass: None
        })
    );
    bindings.remove_data_type("M");
    assert!(!bindings.name_in_use("M"));
}
