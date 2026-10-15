// Modified for Venticorn: distinguish explicit generic arguments from comparisons.
use venticorn::environment::Environment;
use venticorn::expression::{Expression, Terminator};
use venticorn::token::{Token, TokenIter, TokenType};

fn parse(source: &str) -> Expression {
    let mut tokens = TokenIter::new(Token::scan(source));
    Expression::parse_value(&mut tokens, Terminator::Is(TokenType::NewLine))
        .unwrap()
        .0
}

#[test]
fn explicit_argument_lists_round_trip_without_changing_comparisons() {
    for source in [
        "identity<Bool>",
        "(identity)<Bool>(true)",
        "module.identity<Bool>(true)",
        "identity<module.Item>",
        "choose<(Bool -> Bool), module.Item>",
        "make<List<Bool>>",
        "List<Bool>.new",
        "map(identity<Bool>, values)",
        "a < Nat.zero",
        "a < b > c",
        "a < b > (c)",
        "a < module.value > (c)",
        "a < module.value > c",
    ] {
        let rendered = parse(source).to_string();
        assert_eq!(rendered, source);
        assert_eq!(parse(&rendered).to_string(), rendered);
    }
    assert!(
        matches!(parse("a < Nat.zero"), Expression::Binary(_, token, _) if token.token_type == TokenType::LessThan)
    );
    assert!(
        matches!(parse("a < b > (c)"), Expression::Binary(_, token, _) if token.token_type == TokenType::GreaterThan)
    );
    assert!(
        matches!(parse("a < b > c"), Expression::Binary(_, token, _) if token.token_type == TokenType::GreaterThan)
    );
}

#[test]
fn qualified_generic_application_has_function_call_precedence() {
    let Expression::Apply(function, _) = parse("module.identity<Bool>(true)") else {
        panic!("expected the value application");
    };
    let Expression::Apply(qualified, arguments) = *function else {
        panic!("expected explicit type application before value application");
    };
    assert!(
        matches!(*qualified, Expression::Binary(_, token, _) if token.token_type == TokenType::Dot)
    );
    assert!(
        matches!(*arguments, Expression::Grouping(left, _, right) if left.token_type == TokenType::LessThan && right.token_type == TokenType::GreaterThan)
    );
}

#[test]
fn malformed_type_lists_fail_without_panicking() {
    for source in ["identity<>", "identity<Bool,>", "identity<Bool,, Bool>"] {
        let mut tokens = TokenIter::new(Token::scan(source));
        assert!(
            Expression::parse_value(&mut tokens, Terminator::Is(TokenType::NewLine)).is_err(),
            "{source}"
        );
    }
    let mut env = Environment::new_test();
    env.add("define identity<T>(value: T) -> T { value }");
    env.add("let explicit: Bool = identity<Bool>(true)");
    for source in [
        "let bad: Bool = identity<Bool,",
        "let bad: Bool = identity<(Bool -> Bool)",
        "let bad: Bool = identity<Bool",
    ] {
        env.bad(source);
    }
    assert!(!env.bindings.has_identifier("bad"));
}

#[test]
fn comparisons_of_qualified_calls_do_not_look_like_type_arguments() {
    let mut env = Environment::new_test();
    env.add(
        r#"
        type Nat: axiom
        class Nat {
            let 0: Nat = axiom
            let 1: Nat = axiom
            let from_bool: Bool -> Nat = axiom
            define lt(self, other: Nat) -> Bool { axiom }
        }
        theorem comparison {
            Nat.from_bool(false) < Nat.from_bool(true)
        }
        "#,
    );
    for source in [
        "Nat.from_bool(false) < Nat.from_bool(true)",
        "Nat.from_bool(false)<Nat.from_bool(true)",
    ] {
        let Expression::Binary(left, token, right) = parse(source) else {
            panic!("expected a comparison: {source}");
        };
        assert_eq!(token.token_type, TokenType::LessThan);
        assert!(matches!(*left, Expression::Apply(..)));
        assert!(matches!(*right, Expression::Apply(..)));
    }
}

#[test]
fn several_type_arguments_bind_before_higher_order_value_arguments() {
    let mut env = Environment::new_test();
    env.add(
        r#"
        type Nat: axiom
        define maps_to<T, U>(f: T -> U, u: U) -> Bool {
            exists(t: T) { f(t) = u }
        }
        define not2(b: Bool) -> Bool { not b }
        theorem application {
            maps_to<Bool, Bool>(not2, false)
        }
        "#,
    );
    let source = "maps_to<Bool, Bool>(not2, false)";
    let expression = parse(source);
    assert_eq!(expression.to_string(), source);
    let Expression::Apply(function, arguments) = expression else {
        panic!("expected value application");
    };
    let Expression::Apply(_, type_arguments) = *function else {
        panic!("expected type application before value application");
    };
    assert_eq!(type_arguments.flatten_list(true).unwrap().len(), 2);
    assert_eq!(arguments.flatten_list(true).unwrap().len(), 2);
}
