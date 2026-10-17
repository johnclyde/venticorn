// Modified for Venticorn: keep instance identity and declaration metadata through normalization.
use venticorn::acorn_type::AcornType;
use venticorn::acorn_value::{AcornValue, BinaryOp};
use venticorn::clause::Clause;
use venticorn::literal::Literal;
use venticorn::normalizer::Normalizer;

fn instance(left: AcornType, right: AcornType) -> AcornValue {
    let instance_type = AcornType::new_functional(vec![left.clone(), right.clone()], left.clone());
    AcornValue::new_constant(10, "first".into(), vec![left, right], instance_type)
}

#[test]
fn normalized_instances_retain_distinct_order_and_complete_roundtrip_metadata() {
    let nat = AcornType::Data(10, "Nat".into(), vec![]);
    let original = instance(nat.clone(), AcornType::Bool);
    let reversed = instance(AcornType::Bool, nat);
    let mut normalizer = Normalizer::new();
    let term = normalizer.term_from_value(&original, false).unwrap();
    assert_eq!(term, normalizer.term_from_value(&original, false).unwrap());
    let reverse_term = normalizer.term_from_value(&reversed, false).unwrap();
    assert_ne!(term.head, reverse_term.head);
    assert_ne!(term.head_type, reverse_term.head_type);
    let other = AcornValue::new_constant(10, "other".into(), vec![], original.get_type());
    let other_term = normalizer.term_from_value(&other, false).unwrap();
    let clause = Clause::new(vec![Literal::new(true, term, other_term)]);
    normalizer.check_clause(&clause);
    let roundtrip = normalizer.denormalize(&clause);
    roundtrip.validate().unwrap();
    let AcornValue::Binary(BinaryOp::Equals, left, right) = roundtrip else {
        panic!("expected the original constant equality");
    };
    assert!(left.as_ref() == &original || right.as_ref() == &original);
    assert!(left.as_ref() == &other || right.as_ref() == &other);
}
