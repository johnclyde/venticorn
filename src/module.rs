// Modified for Venticorn.

use std::{fmt, path::PathBuf, sync::Arc};

use sha2::{Digest, Sha256};

use crate::compilation;
use crate::environment::Environment;

// Fingerprints identify loaded source snapshots, not proof certificates.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ModuleFingerprint(pub(crate) [u8; 32]);

// Separate source and dependency identity while retaining the complete fingerprint
// used by established callers. Prefix storage is shared across build snapshots.
#[derive(Debug, Clone, Eq)]
pub struct ModuleHash {
    fingerprint: ModuleFingerprint,
    dependencies: ModuleFingerprint,
    prefixes: Arc<[ModuleFingerprint]>,
}

impl PartialEq for ModuleHash {
    fn eq(&self, other: &Self) -> bool {
        self.dependencies == other.dependencies && self.prefixes.last() == other.prefixes.last()
    }
}

impl ModuleHash {
    pub(crate) fn new(
        fingerprint: ModuleFingerprint,
        prefixes: Arc<[ModuleFingerprint]>,
        dependencies: ModuleFingerprint,
    ) -> Self {
        Self {
            fingerprint,
            dependencies,
            prefixes,
        }
    }

    // Inclusive, zero-based complete-line boundary. Missing lines never match.
    pub fn matches_through_line(&self, other: &Self, line: u32) -> bool {
        self.dependencies == other.dependencies
            && self
                .prefixes
                .get(line as usize)
                .is_some_and(|prefix| other.prefixes.get(line as usize) == Some(prefix))
    }

    pub fn fingerprint(&self) -> ModuleFingerprint {
        self.fingerprint
    }
    pub fn dependency_fingerprint(&self) -> ModuleFingerprint {
        self.dependencies
    }
}

// One construction path provides deterministic source and dependency identity.
// All dependency references are sorted before framing, independent of load IDs.
pub(crate) struct ModuleHasher {
    source: Sha256,
    prefixes: Arc<[ModuleFingerprint]>,
    dependencies: Vec<(ModuleRef, ModuleFingerprint)>,
}

impl ModuleHasher {
    pub fn new(text: &str) -> Self {
        let mut source = Sha256::new();
        source.update(b"venticorn:module-logic:v1\0");
        Self::framed(&mut source, text.as_bytes());
        // Preserve raw bytes, including CRLF and final newlines. Hashing framed
        // segments incrementally avoids rescanning each preceding source prefix.
        let mut prefix = Sha256::new();
        prefix.update(b"venticorn:line-prefix:v1\0");
        let prefixes = text
            .split_inclusive('\n')
            .map(|line| {
                Self::framed(&mut prefix, line.as_bytes());
                ModuleFingerprint(prefix.clone().finalize().into())
            })
            .collect::<Vec<_>>()
            .into();
        Self {
            source,
            prefixes,
            dependencies: Vec::new(),
        }
    }

    pub fn add_dependency(&mut self, descriptor: &ModuleRef, fingerprint: ModuleFingerprint) {
        self.dependencies.push((descriptor.clone(), fingerprint));
    }

    fn framed(digest: &mut Sha256, bytes: &[u8]) {
        digest.update((bytes.len() as u64).to_le_bytes());
        digest.update(bytes);
    }

    fn finish_digest(
        mut digest: Sha256,
        dependencies: &[(ModuleRef, ModuleFingerprint)],
    ) -> ModuleFingerprint {
        digest.update((dependencies.len() as u64).to_le_bytes());
        for (descriptor, fingerprint) in dependencies {
            match descriptor {
                ModuleRef::Anonymous => digest.update([0]),
                ModuleRef::Name(name) => {
                    digest.update([1]);
                    Self::framed(&mut digest, name.as_bytes());
                }
                ModuleRef::File(path) => {
                    digest.update([2]);
                    Self::framed(&mut digest, path.as_os_str().as_encoded_bytes());
                }
            }
            digest.update(fingerprint.0);
        }
        ModuleFingerprint(digest.finalize().into())
    }

    pub fn finish(mut self) -> ModuleHash {
        self.dependencies
            .sort_by(|(left, _), (right, _)| left.cmp(right));
        self.dependencies
            .dedup_by(|(left, _), (right, _)| left == right);
        let dependencies = Self::finish_digest(Self::new("").source, &self.dependencies);
        let fingerprint = Self::finish_digest(self.source, &self.dependencies);
        ModuleHash::new(fingerprint, self.prefixes, dependencies)
    }
}

// Loaded state and its fingerprint are kept together without changing public
// module identity or lookup APIs.
pub(crate) struct ModuleRecord {
    pub descriptor: ModuleRef,
    pub state: Module,
    pub hash: Option<ModuleHash>,
}

impl ModuleRecord {
    pub fn anonymous() -> Self {
        Self {
            descriptor: ModuleRef::Anonymous,
            state: Module::None,
            hash: None,
        }
    }

    pub fn loading(descriptor: ModuleRef) -> Self {
        Self {
            descriptor,
            state: Module::Loading,
            hash: None,
        }
    }

    pub fn finish_loading(&mut self, state: Module, hash: Option<ModuleHash>) {
        self.hash = if matches!(state, Module::Ok(_)) {
            hash
        } else {
            None
        };
        self.state = state;
    }
}

// The code in one file is exposed to other Acorn code as a "module".
// You could have two different types both named "MyStruct" but defined in different places.
// Each name is uniquely identified not just by its string name, but also by the module it's defined in.
// When you look at the AcornType object, they should have each have a different ModuleId.
pub type ModuleId = u16;

// Some entities that are created for the prover get their own modules.
// Skolem functions are created during normalization to replace "exists" quantifiers.
pub const SKOLEM: ModuleId = 0;

// The regular module ids start here.
pub const FIRST_NORMAL: ModuleId = 1;

// The Module represents a module that can be in different states of being loaded.
pub enum Module {
    // There is no such module, not even an id for it
    None,

    // The module is in the process of being loaded.
    // Modules that fail on circular import will be in this state forever.
    Loading,

    // The module has been loaded, but there is an error in its code
    Error(compilation::Error),

    // The module has been loaded successfully and we have its environment
    Ok(Environment),
}

// ModuleRef enumerates the different ways a module user can specify a module.
#[derive(Debug, PartialEq, Eq, Hash, Clone, PartialOrd, Ord)]
pub enum ModuleRef {
    // Anything that can't be referred to
    Anonymous,

    // An import chain like foo.bar.baz
    // This sort of module can be either loaded by a project, or referred to in code.
    Name(String),

    // A filename.
    // This sort of module can be loaded by a project, but not referred to in code.
    File(PathBuf),
}

impl fmt::Display for ModuleRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            ModuleRef::Anonymous => write!(f, "<anonymous>"),
            ModuleRef::Name(name) => write!(f, "{}", name),
            ModuleRef::File(path) => write!(f, "{}", path.display()),
        }
    }
}

#[cfg(test)]
mod fingerprint_tests {
    use super::*;

    fn logical_fingerprint(
        text: &str,
        dependencies: Vec<(&ModuleRef, ModuleFingerprint)>,
    ) -> ModuleFingerprint {
        let mut hasher = ModuleHasher::new(text);
        for (descriptor, fingerprint) in dependencies {
            hasher.add_dependency(descriptor, fingerprint);
        }
        hasher.finish().fingerprint()
    }

    fn hash(text: &str) -> ModuleHash {
        ModuleHasher::new(text).finish()
    }

    #[test]
    fn prefix_boundaries_preserve_exact_source_bytes() {
        let original = hash("α😀\nsecond\nthird\n");
        let changed = hash("α😀\nchanged\nthird\n");
        assert!(original.matches_through_line(&changed, 0));
        assert!(!original.matches_through_line(&changed, 1));
        assert!(!original.matches_through_line(&changed, 2));
        assert!(!original.matches_through_line(&original, 3));
        assert!(!original.matches_through_line(&hash("β😀\nsecond\nthird\n"), 0));
        assert!(!original.matches_through_line(&hash("α😀\r\nsecond\r\nthird\r\n"), 0));
        assert!(original.matches_through_line(&hash("α😀\nsecond\nthird\nextra"), 2));
    }

    #[test]
    fn empty_and_final_line_boundaries_are_conservative() {
        assert_eq!(hash(""), hash(""));
        assert!(!hash("").matches_through_line(&hash(""), 0));
        assert!(!hash("a").matches_through_line(&hash("a\n"), 0));
        assert_ne!(hash("a"), hash("a\n"));
        assert!(hash("a\n").matches_through_line(&hash("a\n\n"), 0));
        assert!(!hash("a\n").matches_through_line(&hash("a\n\n"), 1));
        assert!(hash("\n").matches_through_line(&hash("\n"), 0));
        assert!(!hash("\n").matches_through_line(&hash(""), 0));
        assert!(!hash("a").matches_through_line(&hash("a"), u32::MAX));
    }

    #[test]
    fn dependency_identity_is_framed_and_ordered_independently_of_ids() {
        let a = ModuleRef::Name("a".into());
        let b = ModuleRef::Name("b".into());
        let file_a = ModuleRef::File(PathBuf::from("a"));
        let leaf = logical_fingerprint("same source", vec![]);
        let first = logical_fingerprint("parent", vec![(&a, leaf), (&b, leaf)]);
        assert_eq!(
            first,
            logical_fingerprint("parent", vec![(&b, leaf), (&a, leaf)])
        );
        assert_eq!(
            first,
            logical_fingerprint("parent", vec![(&a, leaf), (&a, leaf), (&b, leaf)])
        );
        assert_ne!(
            logical_fingerprint("parent", vec![(&a, leaf)]),
            logical_fingerprint("parent", vec![(&b, leaf)])
        );
        assert_ne!(
            logical_fingerprint("parent", vec![(&a, leaf)]),
            logical_fingerprint("parent", vec![(&file_a, leaf)])
        );
    }
}
