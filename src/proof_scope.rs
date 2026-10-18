//! Immutable lexical authority for proof search and verification reuse.
use std::collections::BTreeSet;
use std::sync::Arc;

use crate::acorn_type::{Class, Typeclass};
use crate::module::ModuleId;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct MembershipKey {
    pub(crate) data: Class,
    pub(crate) class: Typeclass,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ProofScope {
    pub(crate) memberships: Arc<BTreeSet<MembershipKey>>,
    pub(crate) denied_memberships: Arc<BTreeSet<MembershipKey>>,
    pub(crate) imports: Arc<Vec<ModuleId>>,
}

impl ProofScope {
    // These records describe visible declarations, not proof certificates.
    pub fn has_membership(&self, module: ModuleId, name: &str, class: &Typeclass) -> bool {
        let key = MembershipKey {
            data: Class::new(module, name.to_string()),
            class: class.clone(),
        };
        self.memberships.contains(&key) && !self.denied_memberships.contains(&key)
    }

    pub fn has_class_membership(&self, data: &Class, class: &Typeclass) -> bool {
        self.has_membership(data.module_id, &data.name, class)
    }

    pub fn imports(&self) -> &[ModuleId] {
        &self.imports
    }

    pub(crate) fn record_instance(&mut self, module: ModuleId, name: &str, class: &Typeclass) {
        Arc::make_mut(&mut self.memberships).insert(MembershipKey {
            data: Class::new(module, name.to_string()),
            class: class.clone(),
        });
    }

    pub(crate) fn deny_instance(&mut self, module: ModuleId, name: &str, class: &Typeclass) {
        Arc::make_mut(&mut self.denied_memberships).insert(MembershipKey {
            data: Class::new(module, name.to_string()),
            class: class.clone(),
        });
    }

    pub(crate) fn import(&mut self, module: ModuleId) {
        if !self.imports.contains(&module) {
            Arc::make_mut(&mut self.imports).push(module);
        }
    }

    pub(crate) fn include_memberships(&mut self, imported: &ProofScope) {
        if !imported.memberships.is_subset(&self.memberships) {
            Arc::make_mut(&mut self.memberships).extend(imported.memberships.iter().cloned());
        }
    }
}
