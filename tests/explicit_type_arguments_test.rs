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
fn malformed_type_lists_and_pending_evaluation_fail_without_panicking() {
    for source in ["identity<>", "identity<Bool,>", "identity<Bool,, Bool>"] {
        let mut tokens = TokenIter::new(Token::scan(source));
        assert!(
            Expression::parse_value(&mut tokens, Terminator::Is(TokenType::NewLine)).is_err(),
            "{source}"
        );
    }
    let mut env = Environment::new_test();
    env.add("define identity<T>(value: T) -> T { value }");
    env.bad("let bad: Bool = identity<Bool>(true)");
    for source in [
        "let bad: Bool = identity<Bool,",
        "let bad: Bool = identity<(Bool -> Bool)",
        "let bad: Bool = identity<Bool",
    ] {
        env.bad(source);
    }
    assert!(!env.bindings.has_identifier("bad"));
}
