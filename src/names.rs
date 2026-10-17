use std::fmt;

use crate::acorn_type::Typeclass;
use crate::module::ModuleId;

/// How a constant is named in its defining module.
///
/// Instance identity includes the canonical class, even when its displayed name
/// is also used by a different imported class.
#[derive(Hash, Debug, Eq, PartialEq, Clone)]
pub enum LocalName {
    Unqualified(String),
    /// An attribute of a local data type or typeclass.
    Attribute(String, String),
    /// Canonical typeclass, attribute, and local concrete target name.
    Instance(Typeclass, String, String),
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

/// A constant's defining module together with its structured local identity.
#[derive(Hash, Debug, Eq, PartialEq, Clone)]
pub struct GlobalName {
    pub module_id: ModuleId,
    pub local_name: LocalName,
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    #[test]
    fn structured_identity_does_not_depend_on_display_spelling() {
        let left = LocalName::Instance(
            Typeclass {
                module_id: 1,
                name: "Magma".into(),
            },
            "combine".into(),
            "State".into(),
        );
        let right = LocalName::Instance(
            Typeclass {
                module_id: 2,
                name: "Magma".into(),
            },
            "combine".into(),
            "State".into(),
        );
        assert_eq!(left.to_string(), "State.Magma.combine");
        assert_eq!(left.to_string(), right.to_string());
        assert_ne!(left, right);
        let first = GlobalName {
            module_id: 3,
            local_name: left.clone(),
        };
        let other_owner = GlobalName {
            module_id: 4,
            local_name: left,
        };
        let other_class = GlobalName {
            module_id: 3,
            local_name: right,
        };
        assert_eq!(HashSet::from([first, other_owner, other_class]).len(), 3);
        assert_ne!(
            LocalName::Unqualified("State.flag".into()),
            LocalName::Attribute("State".into(), "flag".into()),
        );
    }
}
