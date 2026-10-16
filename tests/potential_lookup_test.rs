// Modified for Venticorn: keep pending generic names outside completed proof values.
use venticorn::acorn_type::AcornType;
use venticorn::binding_map::PotentialValue;
use venticorn::environment::Environment;
use venticorn::expression::Expression;

#[test]
fn lookup_distinguishes_pending_generics_and_canonical_aliases() {
    let mut env = Environment::new_test();
    env.add("define identity<T>(value: T) -> T { value }");
    env.add("let original: Bool = axiom\nlet alias: Bool = original");
    let pending = env.bindings.get_constant_value("identity").unwrap();
    assert!(matches!(&pending, PotentialValue::Unresolved(..)));
    let source = Expression::expect_value("identity");
    let error = pending.value(&source).unwrap_err();
    assert!(
        error.message().contains("requires type arguments"),
        "{error}"
    );
    assert_eq!(error.range(), source.range());
    let alias = env
        .bindings
        .get_constant_value("alias")
        .unwrap()
        .value(&source)
        .unwrap();
    assert_eq!(alias.as_name(), Some((env.module_id, "original")));
    assert_eq!(alias.get_type(), AcornType::Bool);
    alias.validate().unwrap();
    assert!(env.bindings.get_constant_value("missing").is_none());
}

#[test]
fn generic_numeral_readers_return_a_located_error() {
    use venticorn::project::Project;
    let mut env = Environment::new_test();
    env.add("type Number: axiom\nclass Number {\n let 0: Number = axiom\n}\nnumerals Number");
    let number = AcornType::Data(env.module_id, "Number".into(), vec![]);
    // Pending metadata can come from a declaration producer; numeral evaluation must
    // reject it before constructing an application, even when its result type is fixed.
    env.bindings.add_constant(
        "Number.read",
        vec![venticorn::acorn_type::TypeParam::unconstrained("T")],
        AcornType::new_functional(vec![number.clone(), number.clone()], number),
        None,
        None,
    );
    let expression = Expression::expect_value("00");
    let error = env
        .bindings
        .evaluate_value(&Project::new_mock(), &expression, None)
        .unwrap_err();
    assert_eq!(
        error.message(),
        "read function Number.read requires type arguments"
    );
    assert_eq!(error.range(), expression.range());
}
