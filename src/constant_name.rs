//! Compatibility names for callers of the original constant-name API.

pub use crate::names::{GlobalName as GlobalConstantName, LocalName as LocalConstantName};

#[cfg(test)]
mod tests {
    use super::*;
    use crate::acorn_type::Typeclass;
    use std::collections::HashSet;

    #[test]
    fn structured_identity_does_not_depend_on_display_spelling() {
        let left = LocalConstantName::Instance(
            Typeclass {
                module_id: 1,
                name: "Magma".into(),
            },
            "combine".into(),
            "State".into(),
        );
        let right = LocalConstantName::Instance(
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
        let first = GlobalConstantName {
            module_id: 3,
            local_name: left.clone(),
        };
        let other_owner = GlobalConstantName {
            module_id: 4,
            local_name: left,
        };
        let other_class = GlobalConstantName {
            module_id: 3,
            local_name: right,
        };
        assert_eq!(HashSet::from([first, other_owner, other_class]).len(), 3);
        assert_ne!(
            LocalConstantName::Unqualified("State.flag".into()),
            LocalConstantName::Attribute("State".into(), "flag".into()),
        );
    }
}
