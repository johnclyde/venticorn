use venticorn::environment::Environment;
use venticorn::expression::Expression;
use venticorn::project::Project;
use venticorn::statement::Statement;

#[test]
fn operator_aliases_preserve_the_checked_function_identity() {
    let mut env = Environment::new_test();
    env.add(
        r#"
            inductive Item {
                item
            }
            class Item {
                define combine(self, other: Item) -> Item { self }
                let add: (Item, Item) -> Item = Item.combine
            }
            typeclass M: Magma {
                mul: (M, M) -> M
            }
            instance Item: Magma {
                let mul: (Item, Item) -> Item = Item.combine
            }
        "#,
    );
    let evaluate = |text| {
        env.bindings
            .evaluate_value(&Project::new_mock(), &Expression::expect_value(text), None)
            .unwrap()
    };
    assert_eq!(
        evaluate("Item.item + Item.item"),
        evaluate("Item.combine(Item.item, Item.item)")
    );
    assert_eq!(
        evaluate("Magma.mul(Item.item, Item.item)").get_type(),
        evaluate("Item.item").get_type()
    );
    let expected = env.bindings.get_constant_value("Item.combine").unwrap();
    assert_eq!(
        env.bindings.get_constant_value("Item.add").unwrap(),
        expected
    );
    assert_eq!(
        env.bindings.get_constant_value("Item.Magma.mul").unwrap(),
        expected
    );
}

#[test]
fn nonfunction_operators_and_reserved_names_still_reject_without_publication() {
    let mut env = Environment::new_test();
    env.add("type Item: axiom");
    for (member, expected) in [
        (
            "let add: Item = axiom",
            "operator members must have a function type",
        ),
        (
            "let mul: Bool = true",
            "operator members must have a function type",
        ),
        ("let read: (Item, Item) -> Item = axiom", "reserved word"),
        ("let new: Item = axiom", "reserved word"),
    ] {
        let statement = Statement::parse_str(&format!("class Item {{\n{member}\n}}")).unwrap();
        let count = env.nodes.len();
        let scope = env.bindings.proof_scope().clone();
        let error = env
            .add_statement(&mut Project::new_mock(), &statement)
            .unwrap_err();
        assert!(error.message().contains(expected), "{error}");
        assert_eq!(env.nodes.len(), count);
        assert_eq!(env.bindings.proof_scope(), &scope);
    }
    for name in ["Item.add", "Item.mul", "Item.read", "Item.new"] {
        assert!(env.bindings.get_constant_value(name).is_none());
    }
    env.add("class Item {\n define combine(self, other: Item) -> Item { self }\n let add: (Item, Item) -> Item = Item.combine\n}");
    assert_eq!(
        env.bindings.get_constant_value("Item.add").unwrap(),
        env.bindings.get_constant_value("Item.combine").unwrap()
    );
}
