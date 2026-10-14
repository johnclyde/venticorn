// Modified for Venticorn: independent finite-model checks for match lowering.
use venticorn::acorn_type::AcornType;
use venticorn::acorn_value::{AcornValue, BinaryOp};
use venticorn::atom::AtomId;

#[derive(Clone, Debug, PartialEq)]
enum Value {
    Bool(bool),
    Item(Option<bool>),
    Function(String),
    Closure(Vec<AcornType>, Box<AcornValue>, Vec<Value>),
}

fn item_type() -> AcornType {
    AcornType::Data(0, "Item".to_string())
}

fn domain(t: &AcornType) -> Vec<Value> {
    if *t == AcornType::Bool {
        vec![Value::Bool(false), Value::Bool(true)]
    } else {
        assert_eq!(*t, item_type());
        vec![
            Value::Item(None),
            Value::Item(Some(false)),
            Value::Item(Some(true)),
        ]
    }
}

fn assignments(types: &[AcornType]) -> Vec<Vec<Value>> {
    if let Some((first, rest)) = types.split_first() {
        domain(first)
            .into_iter()
            .flat_map(|value| {
                assignments(rest).into_iter().map(move |mut tail| {
                    tail.insert(0, value.clone());
                    tail
                })
            })
            .collect()
    } else {
        vec![vec![]]
    }
}

fn boolean(value: Value) -> bool {
    match value {
        Value::Bool(value) => value,
        other => panic!("expected Boolean, got {:?}", other),
    }
}

// This interpreter selects the matching constructor and evaluates only that branch.
// It does not use the implication/conjunction transformation being tested.
fn evaluate(value: &AcornValue, stack: &[Value]) -> Value {
    match value {
        AcornValue::Variable(index, _) => stack[*index as usize].clone(),
        AcornValue::Bool(value) => Value::Bool(*value),
        AcornValue::Constant(c) if c.name == "Item.empty" => Value::Item(None),
        AcornValue::Constant(c) => Value::Function(c.name.clone()),
        AcornValue::Lambda(vars, body) => {
            Value::Closure(vars.clone(), body.clone(), stack.to_vec())
        }
        AcornValue::Application(app) => {
            let args: Vec<_> = app.args.iter().map(|arg| evaluate(arg, stack)).collect();
            match evaluate(&app.function, stack) {
                Value::Function(name) if name == "Item.wrap" => {
                    Value::Item(Some(boolean(args[0].clone())))
                }
                Value::Function(name) if name == "same" => Value::Bool(args[0] == args[1]),
                Value::Function(name) if name == "identity" => args[0].clone(),
                Value::Closure(vars, body, mut closure_stack) => {
                    assert_eq!(vars.len(), args.len());
                    closure_stack.extend(args);
                    evaluate(&body, &closure_stack)
                }
                other => panic!("unexpected function {:?}", other),
            }
        }
        AcornValue::Binary(op, left, right) => {
            let left = evaluate(left, stack);
            let right = evaluate(right, stack);
            Value::Bool(match op {
                BinaryOp::Equals => left == right,
                BinaryOp::NotEquals => left != right,
                BinaryOp::And => boolean(left) && boolean(right),
                BinaryOp::Or => boolean(left) || boolean(right),
                BinaryOp::Implies => !boolean(left) || boolean(right),
            })
        }
        AcornValue::Not(value) => Value::Bool(!boolean(evaluate(value, stack))),
        AcornValue::ForAll(vars, body) | AcornValue::Exists(vars, body) => {
            let results = assignments(vars).into_iter().map(|values| {
                let mut inner = stack.to_vec();
                inner.extend(values);
                boolean(evaluate(body, &inner))
            });
            Value::Bool(if matches!(value, AcornValue::ForAll(..)) {
                results.clone().all(|value| value)
            } else {
                results.clone().any(|value| value)
            })
        }
        AcornValue::IfThenElse(cond, yes, no) => evaluate(
            if boolean(evaluate(cond, stack)) {
                yes
            } else {
                no
            },
            stack,
        ),
        AcornValue::Match(scrutinee, cases) => {
            let scrutinee = evaluate(scrutinee, stack);
            for (vars, pattern, result) in cases {
                for values in assignments(vars) {
                    let mut inner = stack.to_vec();
                    inner.extend(values);
                    if evaluate(pattern, &inner) == scrutinee {
                        return evaluate(result, &inner);
                    }
                }
            }
            panic!("nonexhaustive test match")
        }
        other => panic!("unexpected finite-model value {:?}", other),
    }
}

fn constant(name: &str, t: AcornType) -> AcornValue {
    AcornValue::new_constant(0, name.to_string(), vec![], t)
}

fn wrap(value: AcornValue) -> AcornValue {
    AcornValue::new_apply(
        constant(
            "Item.wrap",
            AcornType::new_functional(vec![AcornType::Bool], item_type()),
        ),
        vec![value],
    )
}

fn empty() -> AcornValue {
    constant("Item.empty", item_type())
}

fn var(index: AtomId, t: AcornType) -> AcornValue {
    AcornValue::Variable(index, t)
}

fn match_item(
    scrutinee: AcornValue,
    stack_size: AtomId,
    wrapped: AcornValue,
    empty_result: AcornValue,
) -> AcornValue {
    AcornValue::Match(
        Box::new(scrutinee),
        vec![
            (
                vec![AcornType::Bool],
                wrap(var(stack_size, AcornType::Bool)),
                wrapped,
            ),
            (vec![], empty(), empty_result),
        ],
    )
}

fn payload(scrutinee: AcornValue, stack_size: AtomId) -> AcornValue {
    match_item(
        scrutinee,
        stack_size,
        var(stack_size, AcornType::Bool),
        AcornValue::Bool(false),
    )
}

fn call_same(left: AcornValue, right: AcornValue) -> AcornValue {
    AcornValue::new_apply(
        constant(
            "same",
            AcornType::new_functional(vec![left.get_type(), right.get_type()], AcornType::Bool),
        ),
        vec![left, right],
    )
}

fn check_open(value: AcornValue, types: Vec<AcornType>) {
    AcornValue::new_forall(types.clone(), value.clone())
        .validate()
        .expect("test input should be scoped correctly");
    let stack_size = types.len() as AtomId;
    let lowered = value
        .replace_function_equality(stack_size)
        .expand_lambdas(stack_size)
        .replace_match(stack_size)
        .expect("first-order match should lower")
        .expand_lambdas(stack_size);
    assert!(!lowered.contains_match());
    AcornValue::new_forall(types.clone(), lowered.clone())
        .validate()
        .expect("lowering must preserve binder scope and types");
    for stack in assignments(&types) {
        assert_eq!(
            evaluate(&lowered, &stack),
            evaluate(&value, &stack),
            "lowering {} into {} with {:?}",
            value,
            lowered,
            stack
        );
    }
}

fn check(value: AcornValue) {
    check_open(value, vec![]);
}

#[test]
fn match_truth_tables_preserve_both_operands_and_negation() {
    for input in [
        empty(),
        wrap(AcornValue::Bool(false)),
        wrap(AcornValue::Bool(true)),
    ] {
        for b in [false, true] {
            for op in [
                BinaryOp::Equals,
                BinaryOp::NotEquals,
                BinaryOp::And,
                BinaryOp::Or,
                BinaryOp::Implies,
            ] {
                let matched = payload(input.clone(), 0);
                for (left, right) in [
                    (matched.clone(), AcornValue::Bool(b)),
                    (AcornValue::Bool(b), matched),
                ] {
                    let value = AcornValue::Binary(op, Box::new(left), Box::new(right));
                    check(value.clone());
                    check(value.negate());
                }
            }
        }
    }
}

#[test]
fn matches_preserve_outer_and_inner_binder_scopes() {
    let input = var(0, item_type());
    let outer = var(1, AcornType::Bool);
    let matched = payload(input.clone(), 2);
    for op in [BinaryOp::Equals, BinaryOp::NotEquals] {
        let body = AcornValue::Binary(op, Box::new(outer.clone()), Box::new(matched.clone()));
        check_open(body.clone(), vec![item_type(), AcornType::Bool]);
        check(AcornValue::new_forall(
            vec![item_type(), AcornType::Bool],
            body.clone(),
        ));
        check(AcornValue::new_exists(
            vec![item_type(), AcornType::Bool],
            body,
        ));
    }
    // The sibling quantifier originally starts at index 2; lifting the match in
    // the other argument must shift this binder past its case variable.
    let sibling = AcornValue::new_forall(
        vec![AcornType::Bool],
        AcornValue::new_or(var(2, AcornType::Bool), outer.clone()),
    );
    let body = call_same(matched, sibling);
    check_open(body.clone(), vec![item_type(), AcornType::Bool]);
    check(AcornValue::new_forall(
        vec![item_type(), AcornType::Bool],
        body.clone(),
    ));
    check(AcornValue::new_exists(
        vec![item_type(), AcornType::Bool],
        body,
    ));
}

#[test]
fn nested_scrutinees_results_and_relation_arguments_preserve_truth() {
    for input in [
        empty(),
        wrap(AcornValue::Bool(false)),
        wrap(AcornValue::Bool(true)),
    ] {
        let reconstructed = match_item(input.clone(), 0, wrap(var(0, AcornType::Bool)), empty());
        check(AcornValue::new_equals(reconstructed.clone(), input.clone()));
        check(AcornValue::new_equals(input.clone(), reconstructed.clone()));
        check(call_same(reconstructed.clone(), input.clone()));
        check(call_same(input.clone(), reconstructed.clone()));
        check(call_same(reconstructed.clone(), reconstructed.clone()));
        check(payload(reconstructed, 0));
        let nested = match_item(
            input,
            0,
            payload(wrap(var(0, AcornType::Bool)), 1),
            AcornValue::Bool(false),
        );
        check(nested);
    }
}

#[test]
fn matches_mix_with_conditionals_and_lambda_applications() {
    for b in [false, true] {
        let matched = payload(wrap(AcornValue::Bool(b)), 0);
        check(AcornValue::IfThenElse(
            Box::new(matched.clone()),
            Box::new(AcornValue::Bool(true)),
            Box::new(AcornValue::Bool(false)),
        ));
        let data_if = AcornValue::IfThenElse(
            Box::new(AcornValue::Bool(b)),
            Box::new(match_item(
                empty(),
                0,
                wrap(var(0, AcornType::Bool)),
                empty(),
            )),
            Box::new(wrap(AcornValue::Bool(false))),
        );
        check(AcornValue::new_equals(data_if, empty()));
        let lambda = AcornValue::new_lambda(vec![item_type()], payload(var(0, item_type()), 1));
        check(AcornValue::new_apply(
            lambda,
            vec![wrap(AcornValue::Bool(b))],
        ));
        // Exercise both nullary and argument-bearing cases. The wrapped case's
        // lambda captures its case variable as well as binding its own argument.
        for input in [
            empty(),
            wrap(AcornValue::Bool(false)),
            wrap(AcornValue::Bool(true)),
        ] {
            let selected = match_item(
                input.clone(),
                0,
                AcornValue::new_lambda(
                    vec![AcornType::Bool],
                    AcornValue::new_equals(var(0, AcornType::Bool), var(1, AcornType::Bool)),
                ),
                AcornValue::new_lambda(vec![AcornType::Bool], var(0, AcornType::Bool)),
            );
            check(AcornValue::new_apply(selected, vec![AcornValue::Bool(b)]));
            let selected_nested = match_item(
                input.clone(),
                0,
                AcornValue::new_lambda(
                    vec![AcornType::Bool],
                    AcornValue::new_equals(
                        payload(wrap(var(0, AcornType::Bool)), 2),
                        var(1, AcornType::Bool),
                    ),
                ),
                AcornValue::new_lambda(vec![AcornType::Bool], var(0, AcornType::Bool)),
            );
            check(AcornValue::new_apply(
                selected_nested,
                vec![AcornValue::Bool(b)],
            ));
        }
    }
}

#[test]
fn unapplied_higher_order_match_reports_an_error() {
    let lambda = AcornValue::new_lambda(vec![item_type()], payload(var(0, item_type()), 1));
    let proposition = AcornValue::new_apply(
        constant(
            "higher",
            AcornType::new_functional(vec![lambda.get_type()], AcornType::Bool),
        ),
        vec![lambda],
    );
    assert!(proposition
        .replace_match(0)
        .unwrap_err()
        .contains("higher-order"));
}
