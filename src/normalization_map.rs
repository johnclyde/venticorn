use crate::acorn_type::AcornType;
use crate::acorn_value::ConstantInstance;
use crate::atom::{Atom, AtomId};
use crate::clause::Clause;
use crate::constant_map::ConstantMap;
use crate::literal::Literal;
use crate::names::GlobalName;
use crate::term::{Term, TypeId};
use crate::type_map::TypeMap;

/// Own the rich constant and type identities used by one normalizer.
///
/// The component maps retain their checked interning and reverse lookups. Their
/// public compatibility APIs remain available, while production normalization
/// uses this single owner. Equality assumptions remain explicit proof clauses;
/// this map does not introduce aliases or change proof-scope authority.
#[derive(Clone)]
pub struct NormalizationMap {
    constants: ConstantMap,
    types: TypeMap,
}

impl NormalizationMap {
    pub fn new() -> Self {
        Self {
            constants: ConstantMap::new(),
            types: TypeMap::new(),
        }
    }

    /// Intern the complete canonical identity with the existing locality rule.
    pub fn add_constant(&mut self, name: GlobalName, local: bool) -> Atom {
        self.constants.add_constant_named(name, local)
    }

    /// Compatibility spelling for callers already using typed constant names.
    pub fn add_constant_named(&mut self, name: GlobalName, local: bool) -> Atom {
        self.add_constant(name, local)
    }

    pub fn has_constant_named(&self, name: &GlobalName) -> bool {
        self.constants.has_constant_named(name)
    }

    pub fn name_for_global_id(&self, id: AtomId) -> &GlobalName {
        self.constants.name_for_global_id(id)
    }

    pub fn name_for_local_id(&self, id: AtomId) -> &GlobalName {
        self.constants.name_for_local_id(id)
    }

    /// Assign a type ID, preserving the normalized-type check and reserved IDs.
    pub fn add_type(&mut self, acorn_type: &AcornType) -> TypeId {
        self.types.add_type(acorn_type)
    }

    pub fn get_type(&self, id: TypeId) -> &AcornType {
        self.types.get_type(id)
    }

    pub fn check_term(&self, term: &Term) {
        self.types.check_term(term);
    }

    pub fn check_literal(&self, literal: &Literal) {
        self.types.check_literal(literal);
    }

    pub fn check_clause(&self, clause: &Clause) {
        self.types.check_clause(clause);
    }

    /// Intern a fully monomorphic instance, retaining every ordered actual.
    /// The normalizer validates the effective type and all actuals first.
    pub fn term_from_monomorph(&mut self, instance: &ConstantInstance) -> Term {
        self.types.term_from_monomorph(instance)
    }

    pub fn get_monomorph(&self, id: AtomId) -> &ConstantInstance {
        self.types.get_monomorph(id)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::acorn_type::Class;
    use crate::names::LocalName;
    use crate::term::{BOOL, EMPTY};

    #[test]
    fn shared_mapping_preserves_names_phantom_actuals_and_clone_state() {
        let mut map = NormalizationMap::new();
        assert_eq!(map.get_type(EMPTY), &AcornType::Empty);
        assert_eq!(map.get_type(BOOL), &AcornType::Bool);
        let global = GlobalName::new(41, LocalName::Unqualified("f".into()));
        let local = GlobalName::new(42, LocalName::Unqualified("f".into()));
        assert_eq!(
            map.add_constant(global.clone(), false),
            Atom::GlobalConstant(0)
        );
        assert_eq!(
            map.add_constant(local.clone(), true),
            Atom::LocalConstant(0)
        );
        assert_eq!(map.name_for_global_id(0), &global);
        assert_eq!(map.name_for_local_id(0), &local);
        let first = ConstantInstance {
            name: global.clone(),
            params: vec![AcornType::Bool],
            instance_type: AcornType::Bool,
        };
        let second = ConstantInstance {
            params: vec![AcornType::Data(Class::new(43, "Item".into()), vec![])],
            ..first.clone()
        };
        let first_term = map.term_from_monomorph(&first);
        let second_term = map.term_from_monomorph(&second);
        assert_eq!(first_term.head, Atom::Monomorph(0));
        assert_eq!(second_term.head, Atom::Monomorph(1));
        assert_ne!(first_term.head, second_term.head);
        map.check_term(&first_term);
        map.check_clause(&Clause::new(vec![Literal::positive(second_term.clone())]));
        let mut copied = map.clone();
        assert_eq!(copied.get_monomorph(0), &first);
        assert_eq!(copied.get_monomorph(1), &second);
        assert_eq!(copied.term_from_monomorph(&second), second_term);
        assert_eq!(copied.name_for_global_id(0), &global);
        assert_eq!(copied.name_for_local_id(0), &local);
        let later = GlobalName::new(41, LocalName::Unqualified("later".into()));
        copied.add_constant(later.clone(), false);
        assert!(!map.has_constant_named(&later));
    }
}
