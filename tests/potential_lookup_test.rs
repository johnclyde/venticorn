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
    assert!(error.message().contains("unresolved"), "{error}");
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
