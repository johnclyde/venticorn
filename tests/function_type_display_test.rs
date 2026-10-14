// Modified for Venticorn: preserve functional argument grouping in displayed types.
use venticorn::acorn_type::AcornType;
use venticorn::environment::Environment;
use venticorn::expression::{Expression, Terminator};
use venticorn::token::{Token, TokenIter, TokenType};

#[test]
fn nested_function_argument_types_have_unambiguous_parentheses() {
    let unary = AcornType::new_functional(vec![AcornType::Bool], AcornType::Bool);
    let higher = AcornType::new_functional(vec![unary.clone()], AcornType::Bool);
    assert_eq!(higher.to_string(), "(Bool -> Bool) -> Bool");
    let nested = AcornType::new_functional(vec![higher], AcornType::Bool);
    assert_eq!(nested.to_string(), "((Bool -> Bool) -> Bool) -> Bool");
    let multiple = AcornType::new_functional(vec![unary, AcornType::Bool], AcornType::Bool);
    assert_eq!(multiple.to_string(), "(Bool -> Bool, Bool) -> Bool");
    for rendered in [nested.to_string(), multiple.to_string()] {
        let mut tokens = TokenIter::new(Token::scan(&rendered));
        let (expression, _) =
            Expression::parse_type(&mut tokens, Terminator::Is(TokenType::NewLine)).unwrap();
        assert_eq!(expression.to_string(), rendered);
    }
}

#[test]
fn displayed_function_argument_types_match_declared_types() {
    let mut env = Environment::new_test();
    env.add("define both(f: Bool -> Bool) -> Bool { f(true) and f(false) }");
    env.expect_type("both", "(Bool -> Bool) -> Bool");
    env.add("let both_again: (Bool -> Bool) -> Bool = both");
    env.bad("let wrong: (Bool, Bool) -> Bool = both");
    env.add("define or2(a: Bool, b: Bool) -> Bool { a or b }");
    env.add("let or3: (Bool, Bool) -> Bool = or2");
}
