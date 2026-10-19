use std::collections::HashMap;

use crate::acorn_type::AcornType;
use crate::acorn_value::ConstantInstance;

use crate::atom::{Atom, AtomId};
use crate::clause::Clause;
use crate::literal::Literal;
use crate::term::Term;

// Compatibility exports; the term representation owns these identifiers.
pub use crate::term::{TypeId, BOOL, EMPTY};

// The Acorn language allows a rich variety of types, where each value has an AcornType, and where
// functions can be polymorphic.
// The low-level prover only understands simple typing, where each value has a TypeId, and there
// is no polymorphism.
// The TypeMap is a mapping between the two.
#[derive(Clone)]
pub struct TypeMap {
    // type_to_type_id[acorn_type] is the TypeId
    type_to_type_id: HashMap<AcornType, TypeId>,

    // type_id_to_type[type_id] is the AcornType
    type_id_to_type: Vec<AcornType>,

    // Complete instances map to their atom and effective type ID.
    monomorph_to_id: HashMap<ConstantInstance, (Atom, TypeId)>,

    // Reverse entries retain every ordered actual and the canonical owner.
    id_to_monomorph: Vec<ConstantInstance>,
}

impl TypeMap {
    pub fn new() -> TypeMap {
        let mut map = TypeMap {
            type_to_type_id: HashMap::new(),
            type_id_to_type: vec![],
            id_to_monomorph: vec![],
            monomorph_to_id: HashMap::new(),
        };
        map.add_type(&AcornType::Empty);
        map.add_type(&AcornType::Bool);
        map
    }

    // Returns the id for the new type.
    pub fn add_type(&mut self, acorn_type: &AcornType) -> TypeId {
        if let Some(type_id) = self.type_to_type_id.get(acorn_type) {
            return *type_id;
        }
        if !acorn_type.is_normalized() {
            panic!("Type {} is not normalized", acorn_type);
        }
        self.type_id_to_type.push(acorn_type.clone());
        let id = (self.type_id_to_type.len() - 1) as TypeId;
        self.type_to_type_id.insert(acorn_type.clone(), id);
        id
    }

    pub fn get_type(&self, type_id: TypeId) -> &AcornType {
        &self.type_id_to_type[type_id as usize]
    }

    // Panics if the term has an invalid type id, or one that does not match its type.
    // Checks all type ids in the term, recursively.
    pub fn check_term(&self, term: &Term) {
        // The head has type (A -> B) when the term has type B, so the term's type should
        // have been constructed first.
        assert!(term.get_term_type() <= term.get_head_type());

        // Make sure the type you get when applying the head to its arguments is the
        // same as the term type
        let mut calculated_type = self.get_type(term.head_type).clone();
        for arg in &term.args {
            calculated_type = calculated_type.apply(self.get_type(arg.get_term_type()));
        }
        assert_eq!(calculated_type, *self.get_type(term.get_term_type()));

        // Recurse
        for arg in &term.args {
            self.check_term(arg);
        }
    }

    pub fn check_literal(&self, literal: &Literal) {
        self.check_term(&literal.left);
        self.check_term(&literal.right);
        assert_eq!(literal.left.get_term_type(), literal.right.get_term_type());
    }

    pub fn check_clause(&self, clause: &Clause) {
        for literal in &clause.literals {
            self.check_literal(literal);
        }
    }

    // The supplied instance must be fully monomorphic.
    pub fn term_from_monomorph(&mut self, instance: &ConstantInstance) -> Term {
        let (atom, type_id) = if let Some(mapping) = self.monomorph_to_id.get(instance) {
            *mapping
        } else {
            let type_id = self.add_type(&instance.instance_type);
            let id = self.id_to_monomorph.len() as AtomId;
            let atom = Atom::Monomorph(id);
            self.id_to_monomorph.push(instance.clone());
            self.monomorph_to_id
                .insert(instance.clone(), (atom, type_id));
            (atom, type_id)
        };

        Term {
            term_type: type_id,
            head_type: type_id,
            head: atom,
            args: vec![],
        }
    }

    pub fn get_monomorph(&self, id: AtomId) -> &ConstantInstance {
        &self.id_to_monomorph[id as usize]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_type_map_defaults() {
        let map = TypeMap::new();
        assert_eq!(map.get_type(EMPTY), &AcornType::Empty);
        assert_eq!(map.get_type(BOOL), &AcornType::Bool);
    }
}
