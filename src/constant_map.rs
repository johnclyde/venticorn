use std::collections::HashMap;

use crate::atom::{Atom, AtomId};
use crate::constant_name::{GlobalConstantName, LocalConstantName};
use crate::module::{ModuleId, SKOLEM};

// The ConstantKey identifies a constant in the Acorn language.
#[derive(Hash, Debug, Eq, PartialEq, Clone)]
pub struct ConstantKey {
    pub module: ModuleId,
    pub name: LocalConstantName,
}

impl ConstantKey {
    pub fn from_name(name: GlobalConstantName) -> Self {
        Self {
            module: name.module_id,
            name: name.local_name,
        }
    }
}

// In the Acorn language a constant is uniquely identified by its module id and name.
// The low-level prover, on the other hand, just wants each constant to have a
// numerical id.
// The ConstantMap is a mapping between the two.
#[derive(Clone)]
pub struct ConstantMap {
    // For global constant i in the prover, global_constants[i] is the corresponding ConstantKey.
    // The AtomId -> ConstantKey lookup direction.
    global_constants: Vec<Option<ConstantKey>>,

    // For local constant i in the prover, local_constants[i] is the corresponding ConstantKey.
    // The AtomId -> ConstantKey lookup direction.
    local_constants: Vec<Option<ConstantKey>>,

    // Inverse map of constants.
    // The ConstantKey -> AtomId lookup direction.
    // Multiple ConstantKey can map to the same AtomId, when two constants alias to the same thing.
    keymap: HashMap<ConstantKey, Atom>,
}

impl ConstantMap {
    pub fn new() -> ConstantMap {
        ConstantMap {
            global_constants: vec![],
            local_constants: vec![],
            keymap: HashMap::new(),
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
        self.add_constant_key(ConstantKey::from_name(name), local)
    }

    fn add_constant_key(&mut self, key: ConstantKey, local: bool) -> Atom {
        assert_ne!(
            key.module, SKOLEM,
            "skolem constants should not be stored in the ConstantMap"
        );
        if let Some(&atom) = self.keymap.get(&key) {
            return atom;
        }
        let atom = if local {
            let atom_id = self.local_constants.len() as AtomId;
            self.local_constants.push(Some(key.clone()));
            Atom::LocalConstant(atom_id)
        } else {
            let atom_id = self.global_constants.len() as AtomId;
            self.global_constants.push(Some(key.clone()));
            Atom::GlobalConstant(atom_id)
        };
        self.keymap.insert(key, atom);
        atom
    }

    pub fn has_constant(&self, module: ModuleId, name: &str) -> bool {
        self.has_constant_named(&GlobalConstantName::new(
            module,
            LocalConstantName::from_legacy(name),
        ))
    }

    pub fn has_constant_named(&self, name: &GlobalConstantName) -> bool {
        self.keymap
            .contains_key(&ConstantKey::from_name(name.clone()))
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
        let new_key = ConstantKey::from_name(new.clone());
        if self.keymap.contains_key(&new_key) {
            return false;
        }
        let old_key = ConstantKey::from_name(old.clone());
        let Some(&atom) = self.keymap.get(&old_key) else {
            return false;
        };
        self.keymap.insert(new_key, atom);
        true
    }

    pub(crate) fn global_name(&self, id: AtomId) -> GlobalConstantName {
        let key = self.global_constants[id as usize].as_ref().unwrap();
        GlobalConstantName::new(key.module, key.name.clone())
    }

    pub(crate) fn local_name(&self, id: AtomId) -> GlobalConstantName {
        let key = self.local_constants[id as usize].as_ref().unwrap();
        GlobalConstantName::new(key.module, key.name.clone())
    }

    // Get information about a global constant.
    pub fn get_global_info(&self, atom_id: AtomId) -> (ModuleId, String) {
        let key = &self.global_constants[atom_id as usize].as_ref().unwrap();
        (key.module, key.name.to_string())
    }

    // Get information about a local constant.
    pub fn get_local_info(&self, atom_id: AtomId) -> (ModuleId, String) {
        let key = &self.local_constants[atom_id as usize].as_ref().unwrap();
        (key.module, key.name.to_string())
    }
}
