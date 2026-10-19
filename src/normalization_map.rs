use std::collections::HashMap;

use crate::acorn_type::AcornType;
use crate::acorn_value::{AcornValue, ConstantInstance};
use crate::atom::{Atom, AtomId};
use crate::clause::Clause;
use crate::constant_map::ConstantMap;
use crate::literal::Literal;
use crate::module::SKOLEM;
use crate::names::GlobalName;
use crate::term::{Term, TypeId};
use crate::type_map::TypeMap;

/// Own the rich constant and type identities used by one normalizer.
///
/// The component maps retain their checked interning and reverse lookups. Their
/// public compatibility APIs remain available, while production normalization
/// uses this single owner. Equality assumptions remain explicit proof clauses;
/// production normalization does not activate the explicit low-level alias API.
#[derive(Clone)]
pub struct NormalizationMap {
    constants: ConstantMap,
    types: TypeMap,
    constant_types: HashMap<GlobalName, TypeId>,
}

impl NormalizationMap {
    pub fn new() -> Self {
        Self {
            constants: ConstantMap::new(),
            types: TypeMap::new(),
            constant_types: HashMap::new(),
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

    /// Intern a fixed non-generic constant while recording its effective type.
    pub fn term_from_constant(
        &mut self,
        constant: &ConstantInstance,
        local: bool,
    ) -> Result<Term, String> {
        if !constant.params.is_empty() || constant.name.module_id == SKOLEM {
            return Err("expected a non-parameterized ordinary constant".into());
        }
        if !constant.instance_type.is_normalized() {
            return Err("constant type is not normalized".into());
        }
        if let Some(id) = self.constant_types.get(&constant.name) {
            if self.get_type(*id) != &constant.instance_type {
                return Err("constant identity already has a different type".into());
            }
        }
        let type_id = self.add_type(&constant.instance_type);
        let atom = self.add_constant_named(constant.name.clone(), local);
        self.constant_types.insert(constant.name.clone(), type_id);
        Ok(Term::atom(type_id, atom))
    }

    /// Explicit low-level alias registration; this operation grants no proof authority.
    /// The caller must separately establish the defining equality. The target must
    /// have a recorded matching type, and an emitted conflicting atom is never replaced.
    pub fn alias_monomorph(
        &mut self,
        instance: ConstantInstance,
        target: &GlobalName,
        constant_type: &AcornType,
    ) -> Result<(), String> {
        Self::check_alias_metadata(&instance, target, constant_type)?;
        let atom = self
            .constants
            .atom_for_name(target)
            .ok_or("alias target is not registered")?;
        let type_id = *self
            .constant_types
            .get(target)
            .ok_or("alias target has no recorded type")?;
        if self.get_type(type_id) != constant_type {
            return Err("alias target has a different type".into());
        }
        self.types.alias_monomorph(instance, atom, type_id)
    }

    fn check_alias_metadata(
        instance: &ConstantInstance,
        target: &GlobalName,
        constant_type: &AcornType,
    ) -> Result<(), String> {
        if instance.params.is_empty()
            || instance.name.module_id == SKOLEM
            || target.module_id == SKOLEM
            || &instance.instance_type != constant_type
            || !constant_type.is_normalized()
            || instance.params.iter().any(|actual| !actual.is_normalized())
        {
            return Err("invalid instantiated alias type metadata".into());
        }
        AcornValue::Constant(instance.clone()).validate()?;
        Ok(())
    }

    // Validate all rejection paths before interning a previously unseen target.
    pub(crate) fn alias_monomorph_to_constant(
        &mut self,
        instance: ConstantInstance,
        target: &ConstantInstance,
    ) -> Result<(), String> {
        Self::check_alias_metadata(&instance, &target.name, &target.instance_type)?;
        if !target.params.is_empty() {
            return Err("alias target must be a non-parameterized constant".into());
        }
        if let Some((atom, type_id)) = self.types.monomorph_mapping(&instance) {
            if self.constants.atom_for_name(&target.name) != Some(atom)
                || self.get_type(type_id) != &target.instance_type
            {
                return Err("instantiated constant already has a different atom".into());
            }
        }
        self.term_from_constant(target, false)?;
        self.alias_monomorph(instance, &target.name, &target.instance_type)
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

#[cfg(test)]
mod alias_tests {
    use super::*;
    use crate::acorn_type::TypeParam;
    use crate::names::LocalName;

    fn constant(name: &str, params: Vec<AcornType>, instance_type: AcornType) -> ConstantInstance {
        ConstantInstance {
            name: GlobalName::new(8, LocalName::unqualified(name)),
            params,
            instance_type,
        }
    }

    #[test]
    fn explicit_alias_registration_requires_a_typed_target_and_fixed_matching_metadata() {
        let mut map = NormalizationMap::new();
        let target = constant("target", vec![], AcornType::Bool);
        let source = constant("source", vec![AcornType::Bool], AcornType::Bool);
        assert!(map
            .alias_monomorph(source.clone(), &target.name, &AcornType::Bool)
            .is_err());
        map.add_constant_named(target.name.clone(), false);
        assert!(map
            .alias_monomorph(source.clone(), &target.name, &AcornType::Bool)
            .is_err());
        let target_term = map.term_from_constant(&target, false).unwrap();
        for invalid in [
            constant("source", vec![], AcornType::Bool),
            constant(
                "source",
                vec![AcornType::Variable(TypeParam::unconstrained("T"))],
                AcornType::Bool,
            ),
            constant("source", vec![AcornType::Bool], AcornType::Empty),
        ] {
            assert!(map
                .alias_monomorph(invalid, &target.name, &AcornType::Bool)
                .is_err());
        }
        map.alias_monomorph(source.clone(), &target.name, &AcornType::Bool)
            .unwrap();
        map.alias_monomorph(source.clone(), &target.name, &AcornType::Bool)
            .unwrap();
        assert_eq!(map.term_from_monomorph(&source), target_term);
        assert_eq!(map.name_for_global_id(0), &target.name);
        let unaliased = constant("other", vec![AcornType::Bool], AcornType::Bool);
        assert_eq!(map.term_from_monomorph(&unaliased).head, Atom::Monomorph(0));
        assert_eq!(map.get_monomorph(0), &unaliased);
    }

    #[test]
    fn existing_atom_and_type_conflicts_leave_registered_identity_unchanged() {
        let mut map = NormalizationMap::new();
        let target = constant("target", vec![], AcornType::Bool);
        let target_term = map.term_from_constant(&target, false).unwrap();
        let wrong_type = ConstantInstance {
            instance_type: AcornType::functional(vec![AcornType::Bool], AcornType::Bool),
            ..target.clone()
        };
        assert!(map.term_from_constant(&wrong_type, false).is_err());
        assert_eq!(map.term_from_constant(&target, true).unwrap(), target_term);
        let source = constant("source", vec![AcornType::Bool], AcornType::Bool);
        let original = map.term_from_monomorph(&source);
        assert!(map
            .alias_monomorph(source.clone(), &target.name, &AcornType::Bool)
            .is_err());
        assert_eq!(map.term_from_monomorph(&source), original);
        assert_eq!(map.get_monomorph(0), &source);
        let other = constant("other", vec![], AcornType::Bool);
        let other_term = map.term_from_constant(&other, true).unwrap();
        let alias = constant("alias", vec![AcornType::Bool], AcornType::Bool);
        map.alias_monomorph(alias.clone(), &other.name, &AcornType::Bool)
            .unwrap();
        assert!(map
            .alias_monomorph(alias.clone(), &target.name, &AcornType::Bool)
            .is_err());
        assert_eq!(map.term_from_monomorph(&alias), other_term);
        assert_eq!(map.name_for_local_id(0), &other.name);
    }
}
