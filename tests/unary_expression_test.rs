// Modified for Venticorn: distinguish prefix operators from binary subtraction.
use venticorn::expression::Expression;
use venticorn::token::TokenType;

#[test]
fn leading_minus_is_a_prefix_operator_with_arithmetic_precedence() {
    assert_eq!(Expression::expect_value("-1").to_string(), "-1");
    let expression = Expression::expect_value("-a * b");
    match expression {
        Expression::Binary(left, token, _) => {
            assert_eq!(token.token_type, TokenType::Asterisk);
            assert!(
                matches!(*left, Expression::Unary(token, _) if token.token_type == TokenType::Minus)
            );
        }
        _ => panic!("multiplication must be outside prefix negation"),
    }
    let expression = Expression::expect_value("a - -b");
    match expression {
        Expression::Binary(_, token, right) => {
            assert_eq!(token.token_type, TokenType::Minus);
            assert!(
                matches!(*right, Expression::Unary(token, _) if token.token_type == TokenType::Minus)
            );
        }
        _ => panic!("expected binary subtraction"),
    }
}
#[test]
fn prefix_minus_is_guarded_until_the_operand_supports_negation() {
    use venticorn::environment::Environment;
    use venticorn::project::Project;
    let env = Environment::new_test();
    let error = env
        .bindings
        .evaluate_value(
            &Project::new_mock(),
            &Expression::expect_value("-true"),
            None,
        )
        .unwrap_err();
    // Syntax is accepted independently of whether the type defines negation.
    assert!(error.message.contains("no members"), "{error}");
}

// A compact tree description checks meaning rather than merely retaining source parentheses.
fn tree(expression: &Expression) -> String {
    match expression {
        Expression::Singleton(token) => token.to_string(),
        Expression::Grouping(_, child, _) => tree(child),
        Expression::Unary(token, child) => format!("({} {})", token, tree(child)),
        Expression::Binary(left, token, right) => {
            format!("({} {} {})", token, tree(left), tree(right))
        }
        Expression::Apply(function, args) => format!("(apply {} {})", tree(function), tree(args)),
        _ => panic!("unexpected expression in operator fixture"),
    }
}
#[test]
fn negative_operands_keep_their_tree_across_arithmetic_and_member_access() {
    for (source, expected) in [
        ("-a - b", "(- (- a) b)"),
        ("-(a - b)", "(- (- a b))"),
        ("a + -b", "(+ a (- b))"),
        ("a - -b", "(- a (- b))"),
        ("-a * b", "(* (- a) b)"),
        ("-(a * b)", "(- (* a b))"),
        ("-a.suc", "(- (. a suc))"),
        ("(-a).suc", "(. (- a) suc)"),
        ("-f(a)", "(- (apply f a))"),
        ("--a", "(- (- a))"),
        ("not -a < b", "(not (< (- a) b))"),
    ] {
        let parsed = Expression::expect_value(source);
        assert_eq!(parsed.to_string(), source);
        assert_eq!(tree(&parsed), expected, "{source}");
    }
}
