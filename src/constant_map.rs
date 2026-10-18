use std::collections::HashMap;

use crate::atom::{Atom, AtomId};
use crate::module::{ModuleId, SKOLEM};
use crate::names::{GlobalName, LocalName};

/// Compatibility name for the canonical constant identity.
/// ConstantMap stores GlobalName directly; no second key representation exists.
pub type ConstantKey = GlobalName;

// In the Acorn language a constant is uniquely identified by its module id and name.
// The low-level prover, on the other hand, just wants each constant to have a
// numerical id.
// The ConstantMap is a mapping between the two.
#[derive(Clone)]
pub struct ConstantMap {
    // For global constant i in the prover, global_constants[i] is the corresponding GlobalName.
    // Part of the Atom -> GlobalName lookup direction.
    global_constants: Vec<Option<GlobalName>>,

    // For local constant i in the prover, local_constants[i] is the corresponding GlobalName.
    // Part of the Atom -> GlobalName lookup direction.
    local_constants: Vec<Option<GlobalName>>,

    // Inverse map of constants.
    // The GlobalName -> Atom lookup direction.
    // Explicit compatibility aliases may share an atom; normalization never adds them.
    name_to_atom: HashMap<GlobalName, Atom>,
}

impl ConstantMap {
    pub fn new() -> ConstantMap {
        ConstantMap {
            global_constants: vec![],
            local_constants: vec![],
            name_to_atom: HashMap::new(),
        }
    }

    // Assigns an id to this (module, name) pair if it doesn't already have one.
    pub fn add_constant(&mut self, module: ModuleId, name: &str, local: bool) -> Atom {
        self.add_constant_named(GlobalName::new(module, LocalName::from_legacy(name)), local)
    }

    /// Intern a complete canonical name without reparsing its display spelling.
    pub fn add_constant_named(&mut self, name: GlobalName, local: bool) -> Atom {
        assert_ne!(
            name.module_id, SKOLEM,
            "skolem constants should not be stored in the ConstantMap"
        );
        if let Some(&atom) = self.name_to_atom.get(&name) {
            return atom;
        }
        let atom = if local {
            let atom_id = self.local_constants.len() as AtomId;
            self.local_constants.push(Some(name.clone()));
            Atom::LocalConstant(atom_id)
        } else {
            let atom_id = self.global_constants.len() as AtomId;
            self.global_constants.push(Some(name.clone()));
            Atom::GlobalConstant(atom_id)
        };
        self.name_to_atom.insert(name, atom);
        atom
    }

    pub fn has_constant(&self, module: ModuleId, name: &str) -> bool {
        self.has_constant_named(&GlobalName::new(module, LocalName::from_legacy(name)))
    }

    pub fn has_constant_named(&self, name: &GlobalName) -> bool {
        self.name_to_atom.contains_key(name)
    }

    // Compatibility operation: explicitly alias a name to an existing atom.
    // Equality assumptions must instead be retained as proof clauses.
    pub fn add_alias(
        &mut self,
        new_module: ModuleId,
        new_name: &str,
        old_module: ModuleId,
        old_name: &str,
    ) {
        self.add_alias_named(
            &GlobalName::new(new_module, LocalName::from_legacy(new_name)),
            &GlobalName::new(old_module, LocalName::from_legacy(old_name)),
        );
    }

    /// Compatibility operation for an explicitly requested atom alias.
    /// This does not record a proof premise and is not used by normalization.
    pub fn add_alias_named(&mut self, new: &GlobalName, old: &GlobalName) {
        assert!(
            self.maybe_add_alias(new, old),
            "alias needs a new name and an existing target"
        );
    }

    /// Explicitly alias an unused identity to an existing target.
    /// This compatibility operation does not establish or record a proof premise.
    /// Rejected proposals leave the atom inventory unchanged.
    pub fn maybe_add_alias(&mut self, new: &GlobalName, old: &GlobalName) -> bool {
        if self.name_to_atom.contains_key(new) {
            return false;
        }
        let Some(&atom) = self.name_to_atom.get(old) else {
            return false;
        };
        self.name_to_atom.insert(new.clone(), atom);
        true
    }

    /// Borrow the canonical name corresponding to a global AtomId.
    pub fn name_for_global_id(&self, id: AtomId) -> &GlobalName {
        self.global_constants[id as usize].as_ref().unwrap()
    }

    /// Borrow the canonical name corresponding to a local AtomId.
    pub fn name_for_local_id(&self, id: AtomId) -> &GlobalName {
        self.local_constants[id as usize].as_ref().unwrap()
    }

    /// Compatibility name for the borrowed global lookup.
    pub fn get_global_name(&self, id: AtomId) -> &GlobalName {
        self.name_for_global_id(id)
    }

    /// Compatibility name for the borrowed local lookup.
    pub fn get_local_name(&self, id: AtomId) -> &GlobalName {
        self.name_for_local_id(id)
    }

    // Compatibility display accessors. Use the borrowed names for identity.
    pub fn get_global_info(&self, atom_id: AtomId) -> (ModuleId, String) {
        let name = self.name_for_global_id(atom_id);
        (name.module_id, name.local_name.to_string())
    }

    pub fn get_local_info(&self, atom_id: AtomId) -> (ModuleId, String) {
        let name = self.name_for_local_id(atom_id);
        (name.module_id, name.local_name.to_string())
    }
}
