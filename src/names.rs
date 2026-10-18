use std::fmt;

use crate::acorn_type::Typeclass;
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

/// The declaration form that introduces a name into an environment.
/// Converting it to a value identity does not grant instance membership.
#[derive(Hash, Debug, Eq, PartialEq, Clone, PartialOrd, Ord)]
pub enum DefinedName {
    Unqualified(String),
    Attribute(String, String),
    Instance(Typeclass, String, String),
}

impl DefinedName {
    pub fn unqualified(name: &str) -> Self {
        Self::Unqualified(name.to_owned())
    }

    pub fn attribute(owner: &str, member: &str) -> Self {
        Self::Attribute(owner.to_owned(), member.to_owned())
    }

    pub fn instance(class: &Typeclass, member: &str, target: &str) -> Self {
        Self::Instance(class.clone(), member.to_owned(), target.to_owned())
    }

    pub fn is_instance(&self) -> bool {
        matches!(self, Self::Instance(..))
    }

    /// Return an ordinary declaration name without treating an instance as one.
    pub fn to_local(self) -> Option<LocalName> {
        match self {
            Self::Unqualified(name) => Some(LocalName::Unqualified(name)),
            Self::Attribute(owner, member) => Some(LocalName::Attribute(owner, member)),
            Self::Instance(..) => None,
        }
    }

    /// Preserve the exact implementation identity, including its canonical class.
    pub fn into_identity(self) -> LocalName {
        match self {
            Self::Unqualified(name) => LocalName::Unqualified(name),
            Self::Attribute(owner, member) => LocalName::Attribute(owner, member),
            Self::Instance(class, member, target) => LocalName::Instance(class, member, target),
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
        let implementation = DefinedName::instance(&first, "flag", "State").into_identity();
        assert_eq!(implementation, LocalName::instance(&first, "flag", "State"));
        assert_ne!(
            implementation,
            DefinedName::instance(&other, "flag", "State").into_identity()
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
            DefinedName::instance(&class, "flag", "State").to_local(),
            None
        );
    }
}
