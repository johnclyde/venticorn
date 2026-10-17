use std::collections::HashMap;

use crate::atom::{Atom, AtomId};
use crate::constant_name::{GlobalConstantName, LocalConstantName};
use crate::module::{ModuleId, SKOLEM};

/// Compatibility name for the canonical constant identity.
/// ConstantMap stores GlobalConstantName directly; no second key representation exists.
pub type ConstantKey = GlobalConstantName;

// In the Acorn language a constant is uniquely identified by its module id and name.
// The low-level prover, on the other hand, just wants each constant to have a
// numerical id.
// The ConstantMap is a mapping between the two.
#[derive(Clone)]
pub struct ConstantMap {
    // For global constant i in the prover, global_constants[i] is the corresponding GlobalConstantName.
    // The AtomId -> GlobalConstantName lookup direction.
    global_constants: Vec<Option<GlobalConstantName>>,

    // For local constant i in the prover, local_constants[i] is the corresponding GlobalConstantName.
    // The AtomId -> GlobalConstantName lookup direction.
    local_constants: Vec<Option<GlobalConstantName>>,

    // Inverse map of constants.
    // The GlobalConstantName -> AtomId lookup direction.
    // Multiple GlobalConstantName can map to the same AtomId, when two constants alias to the same thing.
    name_to_id: HashMap<GlobalConstantName, Atom>,
}

impl ConstantMap {
    pub fn new() -> ConstantMap {
        ConstantMap {
            global_constants: vec![],
            local_constants: vec![],
            name_to_id: HashMap::new(),
        }
    }

    // Assigns an id to this (module, name) pair if it doesn't already have one.
    pub fn add_constant(&mut self, module: ModuleId, name: &str, local: bool) -> Atom {
        self.add_constant_named(
            GlobalConstantName::new(module, LocalConstantName::from_legacy(name)),
            local,
        )
    }

    /// Intern a complete canonical name without reparsing its display spelling.
    pub fn add_constant_named(&mut self, name: GlobalConstantName, local: bool) -> Atom {
        assert_ne!(
            name.module_id, SKOLEM,
            "skolem constants should not be stored in the ConstantMap"
        );
        if let Some(&atom) = self.name_to_id.get(&name) {
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
        self.name_to_id.insert(name, atom);
        atom
    }

    pub fn has_constant(&self, module: ModuleId, name: &str) -> bool {
        self.has_constant_named(&GlobalConstantName::new(
            module,
            LocalConstantName::from_legacy(name),
        ))
    }

    pub fn has_constant_named(&self, name: &GlobalConstantName) -> bool {
        self.name_to_id.contains_key(name)
    }

    // Make the new module/name an alias to whatever the old one refers to.
    pub fn add_alias(
        &mut self,
        new_module: ModuleId,
        new_name: &str,
        old_module: ModuleId,
        old_name: &str,
    ) {
        self.add_alias_named(
            &GlobalConstantName::new(new_module, LocalConstantName::from_legacy(new_name)),
            &GlobalConstantName::new(old_module, LocalConstantName::from_legacy(old_name)),
        );
    }

    /// Alias one complete identity to an existing atom after an explicit equality.
    pub fn add_alias_named(&mut self, new: &GlobalConstantName, old: &GlobalConstantName) {
        assert!(
            self.maybe_add_alias(new, old),
            "alias needs a new name and an existing target"
        );
    }

    /// Record an equality alias only if the new identity is unused and the target exists.
    /// Rejected proposals leave the atom inventory unchanged.
    pub fn maybe_add_alias(&mut self, new: &GlobalConstantName, old: &GlobalConstantName) -> bool {
        if self.name_to_id.contains_key(new) {
            return false;
        }
        let Some(&atom) = self.name_to_id.get(old) else {
            return false;
        };
        self.name_to_id.insert(new.clone(), atom);
        true
    }

    /// Borrow the canonical identity behind a global atom.
    pub fn get_global_name(&self, id: AtomId) -> &GlobalConstantName {
        self.global_constants[id as usize].as_ref().unwrap()
    }

    /// Borrow the canonical identity behind a local atom.
    pub fn get_local_name(&self, id: AtomId) -> &GlobalConstantName {
        self.local_constants[id as usize].as_ref().unwrap()
    }

    // Compatibility display accessors. Use the borrowed names for identity.
    pub fn get_global_info(&self, atom_id: AtomId) -> (ModuleId, String) {
        let name = self.get_global_name(atom_id);
        (name.module_id, name.local_name.to_string())
    }

    pub fn get_local_info(&self, atom_id: AtomId) -> (ModuleId, String) {
        let name = self.get_local_name(atom_id);
        (name.module_id, name.local_name.to_string())
    }
}
