// Modified for Venticorn: display failures must not prevent solving a typed goal.
use tower_lsp::lsp_types::{Position, Range};
use venticorn::acorn_type::AcornType;
use venticorn::acorn_value::AcornValue;
use venticorn::environment::Environment;
use venticorn::goal::{Goal, GoalContext};

#[test]
fn solve_goal_falls_back_to_its_source_location_for_an_unavailable_type() {
    let env = Environment::new_test();
    let hidden = AcornType::Data(123, "Hidden".to_string());
    let value = AcornValue::new_lambda(vec![hidden.clone()], AcornValue::Variable(0, hidden));
    value.validate().unwrap();
    assert_eq!(
        env.bindings.value_to_code(&value).unwrap_err().error_type(),
        "UnnamedType"
    );
    let range = Range::new(Position::new(6, 4), Position::new(6, 19));
    let context = GoalContext::new(&env, Goal::Solve(value.clone(), range), 7, 6, 6);
    assert_eq!(context.name, "solve at line 7");
    assert_eq!(context.goal.value(), &value);
    assert_eq!(context.goal.range(), range);
    let printable = GoalContext::new(&env, Goal::Solve(AcornValue::Bool(true), range), 7, 6, 6);
    assert_eq!(printable.name, "solve true");
}
