// Modified for Venticorn: explicit typeclass admission expectations.
use venticorn::environment::Environment;

#[test]
#[ignore = "typeclass member admission is not implemented yet"]
fn constant_only_typeclass_is_admitted() {
    let mut env = Environment::new_test();
    env.add(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }
            "#,
    );
}
