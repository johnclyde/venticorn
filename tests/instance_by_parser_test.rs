use tower_lsp::lsp_types::{Position, Range};
use venticorn::statement::{Statement, StatementInfo};
use venticorn::token::{Token, TokenIter};

#[test]
fn instance_member_and_proof_bodies_keep_separate_ranges_and_roundtrip() {
    let source = "instance Item: algebra.Singleton {\n    let value: Item = Item.only\n} by {\n    forall(x: Item) {\n        x = Item.only\n    }\n}";
    let mut tokens = TokenIter::new(Token::scan(&format!(
        "{source}\ntheorem following {{ true }}"
    )));
    let (statement, closing) = Statement::parse(&mut tokens, false).unwrap();
    assert!(closing.is_none());
    let statement = statement.unwrap();
    assert_eq!(statement.to_string(), source);
    assert_eq!(
        statement.range(),
        Range::new(Position::new(0, 0), Position::new(6, 1))
    );
    let StatementInfo::Instance(instance) = statement.statement else {
        panic!("expected instance")
    };
    assert_eq!(instance.type_name.text(), "Item");
    assert_eq!(instance.typeclass.to_string(), "algebra.Singleton");
    assert_eq!(
        instance.body.range(),
        Range::new(Position::new(0, 33), Position::new(2, 1))
    );
    assert_eq!(instance.body.statements.len(), 1);
    assert!(matches!(
        instance.body.statements[0].statement,
        StatementInfo::Let(_)
    ));
    let proof = instance.proof.expect("the by block must be retained");
    assert_eq!(
        proof.range(),
        Range::new(Position::new(2, 5), Position::new(6, 1))
    );
    assert_eq!(proof.statements.len(), 1);
    assert!(matches!(
        proof.statements[0].statement,
        StatementInfo::ForAll(_)
    ));
    assert_eq!(
        proof.statements[0].range(),
        Range::new(Position::new(3, 4), Position::new(5, 5))
    );
    let (following, closing) = Statement::parse(&mut tokens, false).unwrap();
    assert!(closing.is_none());
    let following = following.unwrap();
    assert_eq!(following.first_line(), 7);
    assert!(matches!(following.statement, StatementInfo::Theorem(_)));
}

#[test]
fn optional_and_empty_instance_proofs_are_distinct_and_do_not_consume_the_next_statement() {
    let no_proof = "instance Item: Singleton {\n}\n\ntheorem following { true }";
    let mut tokens = TokenIter::new(Token::scan(no_proof));
    let (statement, _) = Statement::parse(&mut tokens, false).unwrap();
    let statement = statement.unwrap();
    assert_eq!(statement.last_line(), 1);
    assert_eq!(statement.to_string(), "instance Item: Singleton {\n}");
    let StatementInfo::Instance(instance) = statement.statement else {
        panic!("expected instance")
    };
    assert!(instance.proof.is_none());
    let (following, _) = Statement::parse(&mut tokens, false).unwrap();
    assert!(matches!(
        following.unwrap().statement,
        StatementInfo::Theorem(_)
    ));

    // The ordinary optional-by parser allows the keyword on the following line.
    let source = "instance Item: Singleton {}\nby {}\ntheorem following { true }";
    let mut tokens = TokenIter::new(Token::scan(source));
    let (statement, _) = Statement::parse(&mut tokens, false).unwrap();
    let statement = statement.unwrap();
    assert_eq!(statement.last_line(), 1);
    assert_eq!(
        statement.to_string(),
        "instance Item: Singleton {\n} by {\n}"
    );
    let StatementInfo::Instance(instance) = statement.statement else {
        panic!("expected instance")
    };
    let proof = instance
        .proof
        .expect("an explicit empty proof is still present");
    assert!(proof.statements.is_empty());
    assert_eq!(
        proof.range(),
        Range::new(Position::new(1, 3), Position::new(1, 5))
    );
    let (following, _) = Statement::parse(&mut tokens, false).unwrap();
    assert!(matches!(
        following.unwrap().statement,
        StatementInfo::Theorem(_)
    ));
}

#[test]
fn malformed_instance_proofs_report_errors_without_panicking_on_truncated_input() {
    for source in [
        "instance Item: Singleton {} by",
        "instance Item: Singleton {} by true",
        "instance Item: Singleton {} by {",
        "instance Item: Singleton {} by { forall(x: Item) { x = x }",
    ] {
        let error = match Statement::parse_str(source) {
            Ok(_) => panic!("expected a proof syntax error: {source}"),
            Err(error) => error,
        };
        assert!(!error.message().is_empty());
        let range = error.range();
        assert!((range.start.line, range.start.character) <= (range.end.line, range.end.character));
    }
    let source = "instance Item: Singleton { let value: Item = Item.only } by { forall(x: Item) { x = Item.only } }";
    for end in source.char_indices().map(|(i, _)| i).chain([source.len()]) {
        let mut tokens = TokenIter::new(Token::scan(&source[..end]));
        let _ = Statement::parse(&mut tokens, false);
    }
}
