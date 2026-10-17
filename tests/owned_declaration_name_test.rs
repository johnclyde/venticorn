use venticorn::acorn_type::{AcornType, TypeParam, Typeclass};
use venticorn::binding_map::BindingMap;
use venticorn::constant_name::LocalConstantName;

#[test]
fn owned_and_borrowed_inputs_keep_complete_names_and_formals() {
    let class = Typeclass {
        module_id: 11,
        name: "Marked".into(),
    };
    let name = LocalConstantName::attribute("Family", "flag");
    let params = vec![TypeParam {
        name: "T".into(),
        typeclass: Some(class.clone()),
    }];
    let mut owned = BindingMap::new(10);
    let mut borrowed = BindingMap::new(10);
    let a = owned.add_constant_value(name.clone(), params.clone(), AcornType::Bool, None, None);
    let b = borrowed.add_constant_value(&name, params.clone(), AcornType::Bool, None, None);
    assert_eq!(a, b);
    assert_eq!(a.unresolved_params(), params.as_slice());
    assert_eq!(owned.get_constant_value_named(&name), Some(a));
    assert_eq!(borrowed.get_constant_value_named(&name), Some(b));
    let member = LocalConstantName::instance(&class, "flag", "State");
    owned.add_constant_named(member.clone(), vec![], AcornType::Bool, None, None);
    assert!(owned.get_constant_value_named(&member).is_none());
}
