// Modified for Venticorn: generated arithmetic preserves the evaluated expression.
use venticorn::environment::Environment;
use venticorn::expression::Expression;
use venticorn::project::Project;

fn number_environment() -> Environment {
    let mut env = Environment::new_test();
    env.add("type Number: axiom\nclass Number {\n define neg(self) -> Number { axiom }\n define add(self, other: Number) -> Number { axiom }\n define sub(self, other: Number) -> Number { axiom }\n define mul(self, other: Number) -> Number { axiom }\n define suc(self) -> Number { axiom }\n let 0: Number = axiom\n let 1: Number = axiom\n}\nnumerals Number");
    env
}
fn roundtrip(env: &Environment, input: &str, expected_code: &str) {
    let project = Project::new_mock();
    let value = env
        .bindings
        .evaluate_value(&project, &Expression::expect_value(input), None)
        .unwrap();
    let code = env.bindings.value_to_code(&value).unwrap();
    assert_eq!(code, expected_code, "{input}");
    let recovered = env
        .bindings
        .evaluate_value(&project, &Expression::expect_value(&code), None)
        .unwrap();
    recovered.validate().unwrap();
    assert_eq!(value, recovered, "{input} became {code}");
}
#[test]
fn unary_arithmetic_codegen_preserves_precedence_and_receiver_grouping() {
    let env = number_environment();
    for code in [
        "-0 - 1", "-(0 - 1)", "-0 * 1", "-(0 * 1)", "0 + -1", "0 - -1", "--0", "-0.suc", "(-0).suc",
    ] {
        roundtrip(&env, code, code);
    }
    roundtrip(&env, "0.neg", "-0");
}
#[test]
fn function_valued_negation_stays_in_safe_member_notation() {
    let mut env = Environment::new_test();
    env.add("type Number: axiom\nclass Number {\n define neg(self) -> (Number -> Number) { axiom }\n}\nlet a: Number = axiom\nlet b: Number = axiom");
    roundtrip(&env, "(-a)(b)", "a.neg(b)");
}
