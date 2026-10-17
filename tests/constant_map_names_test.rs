use venticorn::acorn_type::Typeclass;
use venticorn::atom::Atom;
use venticorn::constant_map::{ConstantKey, ConstantMap};
use venticorn::constant_name::{GlobalConstantName, LocalConstantName};

fn instance(owner: u16) -> GlobalConstantName {
    GlobalConstantName::new(
        10,
        LocalConstantName::instance(
            &Typeclass {
                module_id: owner,
                name: "Marked".into(),
            },
            "flag",
            "State",
        ),
    )
}

#[test]
fn canonical_constant_interning_keeps_owners_and_atom_locality() {
    let left = instance(11);
    let right = instance(12);
    assert_eq!(left.local_name.to_string(), right.local_name.to_string());
    let key = ConstantKey::from_name(left.clone());
    assert_eq!(key.module, left.module_id);
    assert_eq!(key.name, left.local_name);
    let mut map = ConstantMap::new();
    let a = map.add_constant_named(left.clone(), false);
    let b = map.add_constant_named(right.clone(), false);
    assert_eq!(a, Atom::GlobalConstant(0));
    assert_eq!(b, Atom::GlobalConstant(1));
    assert_eq!(map.add_constant_named(left, true), a);
    let mut local = ConstantMap::new();
    assert_eq!(
        local.add_constant_named(right, true),
        Atom::LocalConstant(0)
    );
}

#[test]
fn legacy_constant_interning_cannot_guess_a_canonical_instance_owner() {
    let mut map = ConstantMap::new();
    let a = map.add_constant_named(instance(11), false);
    let opaque = map.add_constant(10, "State.Marked.flag", false);
    assert_ne!(a, opaque);
    let attribute = GlobalConstantName::new(10, LocalConstantName::attribute("State", "flag"));
    let typed = map.add_constant_named(attribute, false);
    assert_eq!(typed, map.add_constant(10, "State.flag", false));
}

#[test]
fn typed_alias_operations_keep_homonymous_owners_distinct_until_explicit_aliasing() {
    let mut map = ConstantMap::new();
    let old = instance(11);
    let new = instance(12);
    let atom = map.add_constant_named(old.clone(), false);
    assert!(map.has_constant_named(&old));
    assert!(!map.has_constant_named(&new));
    assert!(!map.has_constant(10, "State.Marked.flag"));
    map.add_alias_named(&new, &old);
    assert!(map.has_constant_named(&new));
    assert_eq!(map.add_constant_named(new, false), atom);
    assert!(!map.has_constant(10, "State.Marked.flag"));
    map.add_constant(10, "old", false);
    map.add_alias(10, "new", 10, "old");
    assert!(map.has_constant(10, "new"));
    assert_eq!(
        map.add_constant(10, "new", false),
        map.add_constant(10, "old", false)
    );
}

#[test]
fn checked_alias_proposals_leave_existing_atoms_unchanged_on_failure() {
    let mut map = ConstantMap::new();
    let old = instance(11);
    let new = instance(12);
    assert!(!map.maybe_add_alias(&new, &old));
    assert!(!map.has_constant_named(&new));
    assert!(!map.has_constant_named(&old));
    assert!(!map.maybe_add_alias(&old, &old));
    let atom = map.add_constant_named(old.clone(), false);
    assert_eq!(atom, Atom::GlobalConstant(0));
    assert!(map.maybe_add_alias(&new, &old));
    assert!(!map.maybe_add_alias(&new, &old));
    assert_eq!(map.add_constant_named(new, false), atom);
    let third = instance(13);
    let other = map.add_constant_named(third.clone(), true);
    assert_eq!(other, Atom::LocalConstant(0));
    assert!(!map.maybe_add_alias(&old, &third));
    assert_eq!(map.add_constant_named(old, false), atom);
    assert_eq!(map.add_constant_named(third, true), other);
}
