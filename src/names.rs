use std::fmt;

use crate::acorn_type::{Class, Typeclass};
use crate::module::ModuleId;

/// How a constant is named in its defining module.
///
/// Instance identity includes the canonical class, even when its displayed name
/// is also used by a different imported class.
#[derive(Hash, Debug, Eq, PartialEq, Clone, PartialOrd, Ord)]
pub enum LocalName {
    Unqualified(String),
    /// An attribute of a local data type or typeclass.
    Attribute(String, String),
    /// Canonical typeclass, attribute, and local concrete target name.
    Instance(Typeclass, String, String),
}

// Borrowed compatibility inputs retain the exact structured identity.
impl From<&LocalName> for LocalName {
    fn from(name: &LocalName) -> Self {
        name.clone()
    }
}

impl fmt::Display for LocalName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LocalName::Unqualified(name) => write!(f, "{}", name),
            LocalName::Attribute(class, attr) => write!(f, "{}.{}", class, attr),
            LocalName::Instance(class, attr, target) => {
                write!(f, "{}.{}.{}", target, class.name, attr)
            }
        }
    }
}

impl LocalName {
    // Compatibility for old raw constructors: only an exact one-dot member is classified.
    // A multi-part spelling cannot establish a canonical instance class owner.
    pub(crate) fn from_legacy(name: &str) -> Self {
        if let Some((owner, member)) = name.split_once('.') {
            if !owner.is_empty() && !member.is_empty() && !member.contains('.') {
                return Self::attribute(owner, member);
            }
        }
        Self::unqualified(name)
    }

    pub fn unqualified(name: &str) -> Self {
        Self::Unqualified(name.to_string())
    }

    pub fn attribute(class: &str, attr: &str) -> Self {
        Self::Attribute(class.to_string(), attr.to_string())
    }

    pub fn instance(class: &Typeclass, attr: &str, target: &str) -> Self {
        Self::Instance(class.clone(), attr.to_string(), target.to_string())
    }

    /// Return syntax components for a simple name without guessing an instance owner.
    /// Instance names require the caller to validate their registered canonical scope.
    pub fn name_chain(&self) -> Option<Vec<&str>> {
        match self {
            Self::Unqualified(name) if !name.contains('.') => Some(vec![name]),
            Self::Attribute(owner, member) if !owner.contains('.') && !member.contains('.') => {
                Some(vec![owner, member])
            }
            _ => None,
        }
    }

    pub fn is_qualified(&self) -> bool {
        !matches!(self, Self::Unqualified(_))
    }

    pub fn as_attribute(&self) -> Option<(&str, &str)> {
        match self {
            Self::Attribute(class, attr) => Some((class, attr)),
            _ => None,
        }
    }
}

/// A constant's defining module together with its structured local identity.
#[derive(Hash, Debug, Eq, PartialEq, Clone, PartialOrd, Ord)]
pub struct GlobalName {
    pub module_id: ModuleId,
    pub local_name: LocalName,
}

impl GlobalName {
    /// Compatibility constructor for callers of the former ConstantKey adapter.
    pub fn from_name(name: Self) -> Self {
        name
    }

    pub fn new(module_id: ModuleId, local_name: LocalName) -> Self {
        Self {
            module_id,
            local_name,
        }
    }
}

/// Complete identity of an implementation relationship's member.
/// For `Ring.add<Int>`, retain the canonical owners of both `Ring` and `Int`.
#[derive(Hash, Debug, Eq, PartialEq, Clone, PartialOrd, Ord)]
pub struct InstanceName {
    /// The canonical typeclass, such as `Ring`.
    pub typeclass: Typeclass,
    /// The implemented member, such as `add`.
    pub attribute: String,
    /// The canonical concrete type, such as `Int`.
    pub class: Class,
}

impl fmt::Display for InstanceName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}.{}.{}",
            self.class.name, self.typeclass.name, self.attribute
        )
    }
}

/// The declaration form that introduces a name into an environment.
/// Converting it to a value identity does not grant instance membership.
#[derive(Hash, Debug, Eq, PartialEq, Clone, PartialOrd, Ord)]
pub enum DefinedName {
    Local(LocalName),
    Instance(InstanceName),
}

impl DefinedName {
    pub fn unqualified(name: &str) -> Self {
        Self::Local(LocalName::unqualified(name))
    }

    pub fn attribute(owner: &str, member: &str) -> Self {
        Self::Local(LocalName::attribute(owner, member))
    }

    pub fn instance(class: &Typeclass, member: &str, target: Class) -> Self {
        Self::Instance(InstanceName {
            typeclass: class.clone(),
            attribute: member.to_owned(),
            class: target,
        })
    }

    pub fn is_instance(&self) -> bool {
        matches!(
            self,
            Self::Instance(..) | Self::Local(LocalName::Instance(..))
        )
    }

    /// Borrow an ordinary declaration name without treating an instance as one.
    pub fn as_local(&self) -> Option<&LocalName> {
        match self {
            Self::Local(LocalName::Instance(..)) | Self::Instance(..) => None,
            Self::Local(name) => Some(name),
        }
    }

    /// Return an ordinary declaration name without treating an instance as one.
    pub fn to_local(self) -> Option<LocalName> {
        match self {
            Self::Local(LocalName::Instance(..)) | Self::Instance(..) => None,
            Self::Local(name) => Some(name),
        }
    }

    /// Consume a declaration only in its canonical target's defining module.
    pub fn into_identity_in(self, module: ModuleId) -> Result<LocalName, &'static str> {
        if let Self::Instance(name) = &self {
            if name.class.module_id != module {
                return Err("instance declaration target belongs to a different module");
            }
        }
        Ok(self.into_identity())
    }

    /// Extract the local identity; declaration admission uses `into_identity_in`
    /// to check the target owner before attaching the containing module.
    pub fn into_identity(self) -> LocalName {
        match self {
            Self::Local(name) => name,
            Self::Instance(name) => {
                LocalName::Instance(name.typeclass, name.attribute, name.class.name)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn declaration_forms_preserve_exact_value_identities() {
        assert_eq!(
            DefinedName::unqualified("value").into_identity(),
            LocalName::unqualified("value")
        );
        assert_eq!(
            DefinedName::attribute("Item", "value").into_identity(),
            LocalName::attribute("Item", "value")
        );
        let first = Typeclass {
            module_id: 3,
            name: "Marked".into(),
        };
        let other = Typeclass {
            module_id: 4,
            name: "Marked".into(),
        };
        let implementation =
            DefinedName::instance(&first, "flag", Class::new(5, "State".into())).into_identity();
        assert_eq!(implementation, LocalName::instance(&first, "flag", "State"));
        assert_ne!(
            implementation,
            DefinedName::instance(&other, "flag", Class::new(5, "State".into())).into_identity()
        );
        assert_ne!(implementation, LocalName::attribute("Marked", "flag"));
        assert_ne!(implementation, LocalName::unqualified("State.Marked.flag"));
    }

    #[test]
    fn ordinary_declaration_projection_excludes_instances() {
        assert_eq!(
            DefinedName::unqualified("value").to_local(),
            Some(LocalName::unqualified("value"))
        );
        assert_eq!(
            DefinedName::attribute("Item", "value").to_local(),
            Some(LocalName::attribute("Item", "value"))
        );
        let class = Typeclass {
            module_id: 3,
            name: "Marked".into(),
        };
        assert_eq!(
            DefinedName::instance(&class, "flag", Class::new(5, "State".into())).to_local(),
            None
        );
    }

    #[test]
    fn wrapped_instance_names_do_not_become_ordinary_declarations() {
        let class = Typeclass {
            module_id: 3,
            name: "Marked".into(),
        };
        let name = LocalName::instance(&class, "flag", "State");
        let declaration = DefinedName::Local(name.clone());
        assert!(declaration.is_instance());
        assert_eq!(declaration.clone().to_local(), None);
        assert_eq!(declaration.into_identity(), name);
        let ordinary = DefinedName::Local(LocalName::attribute("State", "flag"));
        assert!(!ordinary.is_instance());
        assert_eq!(
            ordinary.to_local(),
            Some(LocalName::attribute("State", "flag"))
        );
    }

    #[test]
    fn instance_declarations_check_canonical_target_ownership() {
        let class = Typeclass {
            module_id: 3,
            name: "Marked".into(),
        };
        let local = DefinedName::instance(&class, "flag", Class::new(5, "State".into()));
        let foreign = DefinedName::instance(&class, "flag", Class::new(6, "State".into()));
        assert_ne!(local, foreign);
        assert_eq!(
            local.into_identity_in(5),
            Ok(LocalName::instance(&class, "flag", "State"))
        );
        assert_eq!(
            foreign.into_identity_in(5),
            Err("instance declaration target belongs to a different module")
        );
        let wrapped = DefinedName::Local(LocalName::instance(&class, "flag", "State"));
        assert_eq!(
            wrapped.into_identity_in(5),
            Ok(LocalName::instance(&class, "flag", "State"))
        );
    }
}

#[cfg(test)]
mod borrowed_declaration_tests {
    use super::*;

    #[test]
    fn borrowed_projection_retains_ordinary_identity_and_excludes_both_instance_forms() {
        for name in [
            LocalName::unqualified("value"),
            LocalName::attribute("State", "value"),
        ] {
            let declaration = DefinedName::Local(name.clone());
            assert_eq!(declaration.as_local(), Some(&name));
            assert_eq!(declaration.clone().to_local(), Some(name.clone()));
            assert_eq!(declaration.into_identity(), name);
        }
        let class = Typeclass {
            module_id: 3,
            name: "Marked".into(),
        };
        let local = LocalName::instance(&class, "flag", "State");
        for declaration in [
            DefinedName::Local(local.clone()),
            DefinedName::instance(&class, "flag", Class::new(5, "State".into())),
        ] {
            assert!(declaration.as_local().is_none());
            assert!(declaration.is_instance());
            assert_eq!(declaration.into_identity_in(5), Ok(local.clone()));
        }
    }
}
