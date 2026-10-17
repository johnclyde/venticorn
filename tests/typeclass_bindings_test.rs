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

#[test]
fn complete_scoped_descriptors_keep_renamed_and_foreign_bounds() {
    use venticorn::acorn_type::{AcornType, TypeParam};
    let mut bindings = BindingMap::new(2);
    for (name, module) in [("Renamed", 2), ("Foreign", 3)] {
        let param = TypeParam {
            name: name.into(),
            typeclass: Some(Typeclass {
                module_id: module,
                name: "Magma".into(),
            }),
        };
        let value = bindings.add_arbitrary_type_param(param.clone());
        assert_eq!(value, AcornType::Arbitrary(param.clone()));
        assert_eq!(bindings.get_type_for_name(name), Some(&value));
        assert_eq!(value.to_generic(), AcornType::Variable(param));
        bindings.remove_data_type(name);
        assert!(!bindings.name_in_use(name));
    }
    let param = TypeParam::unconstrained("Open");
    assert_eq!(
        bindings.add_arbitrary_type_param(param.clone()),
        AcornType::Arbitrary(param)
    );
    assert_eq!(
        bindings.add_arbitrary_type("Legacy"),
        AcornType::Arbitrary(TypeParam::unconstrained("Legacy"))
    );
}

#[test]
fn class_definition_metadata_keeps_canonical_bounds_and_phantom_attributes() {
    use venticorn::acorn_type::{AcornType, Typeclass};
    use venticorn::environment::Environment;
    let mut env = Environment::new_test();
    env.add("typeclass T: Marked {\n flag: Bool\n keep: T -> T\n}");
    let class = env
        .bindings
        .get_typeclass_for_name("Marked")
        .unwrap()
        .clone();
    let info = env.bindings.get_typeclass_info(&class).unwrap();
    assert_eq!(info.instance_param.name, "T");
    assert_eq!(info.instance_param.typeclass.as_ref(), Some(&class));
    assert_eq!(info.attributes.len(), 2);
    assert_eq!(info.attributes["flag"], AcornType::Bool);
    let formal = AcornType::Variable(info.instance_param.clone());
    assert_eq!(
        info.attributes["keep"],
        AcornType::new_functional(vec![formal.clone()], formal)
    );
    assert!(env
        .bindings
        .get_typeclass_info(&Typeclass {
            module_id: class.module_id + 1,
            name: class.name.clone(),
        })
        .is_none());
    env.bad("typeclass U: Broken {\n good: U\n bad: Missing\n}");
    assert!(env
        .bindings
        .get_typeclass_info(&Typeclass {
            module_id: env.module_id,
            name: "Broken".into(),
        })
        .is_none());
    env.add("typeclass U: Broken {\n good: U\n}");
    let other = env.bindings.get_typeclass_for_name("Broken").unwrap();
    assert!(env.bindings.get_typeclass_info(other).is_some());
}
