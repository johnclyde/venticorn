use venticorn::acorn_type::{AcornType, TypeParam, Typeclass};
use venticorn::acorn_value::AcornValue;
use venticorn::binding_map::BindingMap;
use venticorn::constant_name::{GlobalConstantName, LocalConstantName};

#[test]
fn prepared_instance_metadata_requires_exact_owner_but_not_published_membership() {
    let mut bindings = BindingMap::new(10);
    let class = Typeclass {
        module_id: 11,
        name: "Marked".into(),
    };
    let member = LocalConstantName::instance(&class, "flag", "State");
    bindings.add_constant_named(
        &member,
        vec![],
        AcornType::Bool,
        Some(AcornValue::Bool(true)),
        None,
    );
    assert!(bindings.get_constant_value_named(&member).is_none());
    assert_eq!(
        bindings.get_definition_named(&member),
        Some(&AcornValue::Bool(true))
    );
    assert_eq!(
        bindings.get_definition("State.Marked.flag"),
        Some(&AcornValue::Bool(true))
    );
    bindings.mark_as_theorem("State.Marked.flag");
    assert!(bindings.is_theorem_named(&member));
    for wrong in [
        LocalConstantName::instance(
            &Typeclass {
                module_id: 12,
                name: "Marked".into(),
            },
            "flag",
            "State",
        ),
        LocalConstantName::unqualified("State.Marked.flag"),
        LocalConstantName::attribute("State.Marked", "flag"),
    ] {
        assert!(bindings.get_definition_named(&wrong).is_none());
        assert!(bindings.get_definition_and_params_named(&wrong).is_none());
        assert!(!bindings.is_theorem_named(&wrong));
    }
}

#[test]
fn named_definition_metadata_retains_phantom_bounds_and_excludes_alias_ownership() {
    let mut bindings = BindingMap::new(10);
    let name = LocalConstantName::attribute("Marked", "flag");
    let params = vec![
        TypeParam {
            name: "M".into(),
            typeclass: Some(Typeclass {
                module_id: 11,
                name: "Marked".into(),
            }),
        },
        TypeParam::unconstrained("U"),
    ];
    bindings.add_constant_named(
        &name,
        params.clone(),
        AcornType::Bool,
        Some(AcornValue::Bool(true)),
        None,
    );
    let (definition, found) = bindings.get_definition_and_params_named(&name).unwrap();
    assert_eq!(definition, &AcornValue::Bool(true));
    assert_eq!(found, params.as_slice());
    let value = bindings.get_constant_value_named(&name).unwrap();
    let alias = LocalConstantName::unqualified("alias");
    bindings.add_alias_named(&alias, GlobalConstantName::new(10, name), value);
    bindings.mark_as_theorem("alias");
    assert!(bindings.get_definition_named(&alias).is_none());
    assert!(bindings.get_definition_and_params_named(&alias).is_none());
    assert!(!bindings.is_theorem_named(&alias));
}
