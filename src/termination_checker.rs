// Modified for Venticorn: reject recursive escapes and inspect every supplied argument.
use crate::acorn_value::AcornValue;
use crate::atom::AtomId;
use crate::constant_name::{GlobalConstantName, LocalConstantName};
use crate::module::ModuleId;

/// Proves termination when one original argument strictly decreases at every recursive use.
/// This is intentionally conservative: decreasing different arguments in different branches
/// does not prove termination, and passing the recursive function as a value is rejected.
pub struct TerminationChecker {
    function_name: GlobalConstantName,
    // Each stack variable maps to its original argument ancestor, if known.
    substructure_map: Vec<Option<AtomId>>,
    always_strict_sub: Vec<bool>,
    recursive: bool,
}

impl TerminationChecker {
    pub fn new(module: ModuleId, function_name: String, num_args: usize) -> Self {
        let ambiguous = function_name.matches('.').count() > 1;
        let mut checker = Self::new_named(
            GlobalConstantName::new(module, LocalConstantName::from_legacy(&function_name)),
            num_args,
        );
        // A raw multi-part spelling cannot identify its canonical instance class.
        // Compatibility callers must use the typed constructor for that case.
        if ambiguous {
            checker.recursive = true;
            checker.always_strict_sub.fill(false);
        }
        checker
    }

    pub(crate) fn new_named(function_name: GlobalConstantName, num_args: usize) -> Self {
        Self {
            function_name,
            substructure_map: (0..num_args).map(|i| Some(i as AtomId)).collect(),
            always_strict_sub: vec![true; num_args],
            recursive: false,
        }
    }

    fn traverse(&mut self, value: &AcornValue) {
        match value {
            AcornValue::Variable(..) | AcornValue::Bool(..) => {}
            AcornValue::Constant(_) => {
                if value.constant_name() == Some(&self.function_name) {
                    self.recursive = true;
                    self.always_strict_sub.fill(false);
                }
            }
            AcornValue::Lambda(args, body)
            | AcornValue::ForAll(args, body)
            | AcornValue::Exists(args, body) => {
                let size = self.substructure_map.len();
                self.substructure_map.resize(size + args.len(), None);
                self.traverse(body);
                self.substructure_map.truncate(size);
            }
            AcornValue::Not(value) => self.traverse(value),
            AcornValue::Binary(_, left, right) => {
                self.traverse(left);
                self.traverse(right);
            }
            AcornValue::IfThenElse(condition, left, right) => {
                self.traverse(condition);
                self.traverse(left);
                self.traverse(right);
            }
            AcornValue::Application(app) => {
                // Borrow arguments from every curried layer in their original order.
                // Rebuilding the application would clone entire argument subtrees.
                let mut function = app.function.as_ref();
                let mut layers = vec![app.args.as_slice()];
                while let AcornValue::Application(inner) = function {
                    layers.push(inner.args.as_slice());
                    function = inner.function.as_ref();
                }
                let args: Vec<_> = layers.into_iter().rev().flatten().collect();

                if function.constant_name() == Some(&self.function_name) {
                    self.recursive = true;
                    for (i, decreasing) in self.always_strict_sub.iter_mut().enumerate() {
                        let strict = match args.get(i) {
                            Some(AcornValue::Variable(j, _)) => {
                                let j = *j as usize;
                                i != j && self.substructure_map.get(j) == Some(&Some(i as AtomId))
                            }
                            _ => false,
                        };
                        *decreasing &= strict;
                    }
                } else {
                    self.traverse(function);
                }
                for arg in args {
                    self.traverse(arg);
                }
            }
            AcornValue::Match(scrutinee, cases) => {
                self.traverse(scrutinee);
                let ancestor = match scrutinee.as_ref() {
                    AcornValue::Variable(i, _) => {
                        self.substructure_map.get(*i as usize).copied().flatten()
                    }
                    _ => None,
                };
                let size = self.substructure_map.len();
                for (args, pattern, result) in cases {
                    self.substructure_map.resize(size + args.len(), ancestor);
                    self.traverse(pattern);
                    self.traverse(result);
                    self.substructure_map.truncate(size);
                }
            }
        }
    }

    /// A checker is used for exactly one function body.
    pub fn check(&mut self, value: &AcornValue) -> bool {
        self.traverse(value);
        !self.recursive || self.always_strict_sub.contains(&true)
    }

    pub fn is_recursive(&self) -> bool {
        self.recursive
    }
}

#[cfg(test)]
mod identity_tests {
    use super::*;
    use crate::acorn_type::{AcornType, Typeclass};

    #[test]
    fn raw_instance_spelling_cannot_bypass_canonical_recursive_identity() {
        let class = Typeclass {
            module_id: 11,
            name: "Marked".into(),
        };
        let name =
            GlobalConstantName::new(10, LocalConstantName::instance(&class, "flag", "State"));
        let value = AcornValue::constant_named(name.clone(), vec![], AcornType::Bool);
        assert!(!TerminationChecker::new(10, "State.Marked.flag".into(), 0).check(&value));
        assert!(!TerminationChecker::new_named(name.clone(), 0).check(&value));
        let foreign = GlobalConstantName::new(
            10,
            LocalConstantName::instance(
                &Typeclass {
                    module_id: 12,
                    name: "Marked".into(),
                },
                "flag",
                "State",
            ),
        );
        assert!(TerminationChecker::new_named(foreign, 0).check(&value));
    }
}
