// Modified for Venticorn: prefix notation uses the type's checked neg method.
use tower_lsp::lsp_types::{Position, Range};
use venticorn::acorn_type::AcornType;
use venticorn::environment::Environment;
use venticorn::expression::Expression;
use venticorn::project::Project;

#[test]
fn unary_minus_evaluates_to_the_same_typed_value_as_its_member_call() {
    let mut env = Environment::new_test();
    env.add("type Number: axiom\nclass Number {\n define neg(self) -> Number { axiom }\n define sub(self, other: Number) -> Number { axiom }\n}\nlet a: Number = axiom\nlet b: Number = axiom");
    let project = Project::new_mock();
    for (operator, explicit) in [
        ("-a", "a.neg"),
        ("a - -b", "Number.sub(a, b.neg)"),
        ("--a", "a.neg.neg"),
    ] {
        let value = env
            .bindings
            .evaluate_value(&project, &Expression::expect_value(operator), None)
            .unwrap();
        let expected = env
            .bindings
            .evaluate_value(&project, &Expression::expect_value(explicit), None)
            .unwrap();
        value.validate().unwrap();
        assert_eq!(value, expected);
    }
    let error = env
        .bindings
        .evaluate_value(
            &project,
            &Expression::expect_value("-a"),
            Some(&AcornType::Bool),
        )
        .unwrap_err();
    assert!(error.message().contains("expected type"), "{error}");
}
#[test]
fn unary_minus_requires_a_method_on_the_operand_type() {
    let mut env = Environment::new_test();
    env.add("type Number: axiom\nlet a: Number = axiom");
    let error = env
        .bindings
        .evaluate_value(&Project::new_mock(), &Expression::expect_value("-a"), None)
        .unwrap_err();
    assert_eq!(error.message(), "unknown attribute 'Number.neg'");
    assert_eq!(
        error.range(),
        Range::new(Position::new(0, 0), Position::new(0, 1))
    );
    env.bad("class Number {\n let neg: Number = axiom\n}");
}
#[test]
fn unary_minus_uses_imported_type_identity_even_through_an_alias() {
    let mut project = Project::new_mock();
    project.mock(
        "/mock/numbers.ac",
        "type Number: axiom\nclass Number {\n define neg(self) -> Number { axiom }\n}",
    );
    project.mock("/mock/main.ac", "from numbers import Number\ntype Alias: Number\nlet a: Alias = axiom\ntheorem identity { -a = a.neg }");
    assert_eq!(
        project.sync_build().0,
        venticorn::builder::BuildStatus::Good
    );
}
#[test]
fn actual_verifier_proves_negation_and_rejects_a_false_negative_equation() {
    use std::fs;
    use std::process::Command;
    let root = std::env::temp_dir().join(format!("venticorn_unary_{}", std::process::id()));
    fs::create_dir_all(&root).unwrap();
    let definitions = "inductive Sign {\n positive\n negative\n}\nclass Sign {\n define neg(self) -> Sign { match self { Sign.positive { Sign.negative } Sign.negative { Sign.positive } } }\n define mul(self, other: Sign) -> Sign { if other = Sign.positive { self } else { -self } }\n}\n";
    for (name, theorem, success) in [
        (
            "positive",
            "theorem product { (-Sign.positive) * (-Sign.positive) = Sign.positive }",
            true,
        ),
        (
            "negative",
            "theorem false_equation { -Sign.positive = Sign.positive }",
            false,
        ),
    ] {
        fs::write(
            root.join(format!("{name}.ac")),
            format!("{definitions}{theorem}\n"),
        )
        .unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_verify"))
            .env("VENTICORN_LIBRARY", &root)
            .arg(name)
            .output()
            .unwrap();
        let text = format!(
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(output.status.success(), success, "{text}");
        if success {
            assert!(text.contains("1/1 OK"), "{text}");
        } else {
            assert_eq!(output.status.code(), Some(1), "{text}");
            assert!(text.contains("Build completed with warnings."), "{text}");
            assert!(text.contains("0/1 OK"), "{text}");
            assert!(
                [
                    "could not be verified",
                    "stopped after hitting constraints",
                    "timed out after"
                ]
                .iter()
                .any(|reason| text.contains(&format!("false_equation {reason}"))),
                "{text}"
            );
            assert!(!text.contains("internal error"), "{text}");
            assert!(!text.contains("panicked"), "{text}");
        }
        assert!(!text.contains("error:"), "{text}");
    }
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn neg_with_an_extra_argument_is_not_formatted_as_subtraction() {
    let mut env = Environment::new_test();
    env.add("type Number: axiom\nclass Number {\n define neg(self, other: Number) -> Number { axiom }\n}\nlet a: Number = axiom\nlet b: Number = axiom");
    let project = Project::new_mock();
    let value = env
        .bindings
        .evaluate_value(
            &project,
            &Expression::expect_value("Number.neg(a, b)"),
            None,
        )
        .unwrap();
    assert_eq!(env.bindings.value_to_code(&value).unwrap(), "a.neg(b)");
}
