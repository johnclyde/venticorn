// Modified for Venticorn: bounded, finalized verification metadata on disk.
use std::collections::{BTreeMap, BTreeSet};
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::acorn_type::AcornType;
use crate::acorn_value::{AcornValue, BinaryOp};
use crate::build_cache::PremiseSet;
use crate::goal::{Goal, GoalContext};
use crate::module::{ModuleHash, ModuleId, ModuleRef, FIRST_NORMAL};

const MAX_RECORD_BYTES: u64 = 16 * 1024;
const SCHEMA: u32 = 2;
static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);

// Existing constructors retain in-process reuse. Disk access is explicitly enabled.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CachePolicy {
    Disabled,
    MemoryOnly,
    ReadOnly,
    ReadWrite,
}

// Describes the compiled scoring policy, including its permitted runtime fallback.
// This does not claim that every search actually used the ONNX backend.
pub fn checker_identity() -> String {
    format!(
        "{}:{}",
        env!("VENTICORN_CHECKER_ID"),
        if cfg!(feature = "onnx") {
            "onnx-with-heuristic-fallback"
        } else {
            "heuristic-only"
        }
    )
}

#[derive(Clone, Debug)]
pub(crate) struct PersistentCache {
    directory: PathBuf,
    root: [u8; 32],
    writable: bool,
}

// Only canonical identities of currently loaded modules are created or resolved.
// Deserializing a File identity never accesses that path.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub(crate) enum HintModule {
    Name(String),
    File(PathBuf),
}

impl HintModule {
    pub(crate) fn from_loaded(module: &ModuleRef) -> Option<Self> {
        match module {
            ModuleRef::Name(name) => Some(Self::Name(name.clone())),
            ModuleRef::File(path) => Some(Self::File(path.canonicalize().ok()?)),
            ModuleRef::Anonymous => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct HintGroup {
    module: HintModule,
    names: BTreeSet<String>,
}

// No old values or ranges are trusted as parsed proof obligations. A matching
// record is promoted using this process's fresh goals and complete line hashes.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct DiskRecord {
    schema: u32,
    checker: String,
    root: [u8; 32],
    module: [u8; 32],
    source: [u8; 32],
    dependencies: [u8; 32],
    goal_policy: [u8; 32],
    hints: BTreeMap<String, Vec<HintGroup>>,
}

impl DiskRecord {
    // Guidance must never affect whether old successful results match current goals.
    fn same_result_identity(&self, other: &Self) -> bool {
        self.schema == other.schema
            && self.checker == other.checker
            && self.root == other.root
            && self.module == other.module
            && self.source == other.source
            && self.dependencies == other.dependencies
            && self.goal_policy == other.goal_policy
    }

    pub(crate) fn with_premises(mut self, premises: &BTreeMap<String, PremiseSet>) -> Self {
        let mut size = 0usize;
        for (theorem, modules) in premises {
            size = size.saturating_add(theorem.len().saturating_add(8));
            if size > MAX_RECORD_BYTES as usize {
                self.hints.clear();
                return self;
            }
            let mut groups = vec![];
            for (module, names) in modules {
                let Some(module) = HintModule::from_loaded(module) else {
                    self.hints.clear();
                    return self;
                };
                size = size.saturating_add(match &module {
                    HintModule::Name(name) => name.len().saturating_add(24),
                    HintModule::File(path) => path.as_os_str().len().saturating_add(24),
                });
                for name in names {
                    size = size.saturating_add(name.len().saturating_add(4));
                }
                if size > MAX_RECORD_BYTES as usize {
                    self.hints.clear();
                    return self;
                }
                groups.push(HintGroup {
                    module,
                    names: names.clone(),
                });
            }
            self.hints.insert(theorem.clone(), groups);
        }
        self
    }
}

struct BoundedBytes(Vec<u8>);
impl Write for BoundedBytes {
    fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
        if bytes.len() > MAX_RECORD_BYTES as usize - self.0.len() {
            return Err(std::io::Error::other("cache record is too large"));
        }
        self.0.extend_from_slice(bytes);
        Ok(bytes.len())
    }
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

fn record_bytes(record: &DiskRecord) -> Option<Vec<u8>> {
    let mut output = BoundedBytes(Vec::new());
    serde_json::to_writer(&mut output, record).ok()?;
    Some(output.0)
}

fn frame(hash: &mut Sha256, bytes: &[u8]) {
    hash.update((bytes.len() as u64).to_le_bytes());
    hash.update(bytes);
}

fn module_identity(module: &ModuleRef) -> Option<[u8; 32]> {
    let mut hash = Sha256::new();
    match module {
        ModuleRef::Anonymous => return None,
        ModuleRef::Name(name) => {
            hash.update([1]);
            frame(&mut hash, name.as_bytes());
        }
        ModuleRef::File(path) => {
            hash.update([2]);
            frame(
                &mut hash,
                path.canonicalize().ok()?.as_os_str().as_encoded_bytes(),
            );
        }
    }
    Some(hash.finalize().into())
}

impl PersistentCache {
    pub(crate) fn new(root: &Path, writable: bool) -> Option<Self> {
        let root = root.canonicalize().ok()?;
        let mut hash = Sha256::new();
        frame(&mut hash, root.as_os_str().as_encoded_bytes());
        Some(Self {
            directory: root.join(".venticorn-cache"),
            root: hash.finalize().into(),
            writable,
        })
    }

    pub(crate) fn record(
        &self,
        module: &ModuleRef,
        hash: &ModuleHash,
        goals: &[GoalContext],
        resolve: impl Fn(ModuleId) -> Option<ModuleRef>,
    ) -> Option<DiskRecord> {
        Some(DiskRecord {
            schema: SCHEMA,
            checker: checker_identity(),
            root: self.root,
            module: module_identity(module)?,
            source: hash.fingerprint().0,
            dependencies: hash.dependency_fingerprint().0,
            goal_policy: goal_policy(goals, &resolve)?,
            hints: BTreeMap::new(),
        })
    }

    fn filename(&self, module: &[u8; 32]) -> PathBuf {
        let mut hash = Sha256::new();
        hash.update(self.root);
        hash.update(module);
        self.directory.join(format!("{:x}.json", hash.finalize()))
    }

    fn directory_is_safe(&self) -> bool {
        fs::symlink_metadata(&self.directory)
            .is_ok_and(|metadata| metadata.is_dir() && !metadata.file_type().is_symlink())
    }

    fn read(&self, module: &[u8; 32]) -> Option<DiskRecord> {
        if !self.directory_is_safe() {
            return None;
        }
        let path = self.filename(module);
        let metadata = fs::symlink_metadata(&path).ok()?;
        if !metadata.is_file()
            || metadata.file_type().is_symlink()
            || metadata.len() > MAX_RECORD_BYTES
        {
            return None;
        }
        let mut bytes = Vec::new();
        File::open(path)
            .ok()?
            .take(MAX_RECORD_BYTES + 1)
            .read_to_end(&mut bytes)
            .ok()?;
        if bytes.len() as u64 > MAX_RECORD_BYTES {
            return None;
        }
        serde_json::from_slice(&bytes).ok()
    }

    pub(crate) fn matches(&self, record: &DiskRecord) -> bool {
        self.read(&record.module)
            .is_some_and(|stored| stored.same_result_identity(record))
    }

    pub(crate) fn advisory_premises(
        &self,
        module: &ModuleRef,
        resolve: impl Fn(&HintModule) -> Option<ModuleRef>,
    ) -> Option<BTreeMap<String, PremiseSet>> {
        let module = module_identity(module)?;
        let stored = self.read(&module)?;
        if stored.schema != SCHEMA
            || stored.checker != checker_identity()
            || stored.root != self.root
            || stored.module != module
        {
            return None;
        }
        let mut answer = BTreeMap::new();
        for (theorem, groups) in stored.hints {
            let mut premises = PremiseSet::new();
            let mut resolved = true;
            for group in groups {
                let Some(module) = resolve(&group.module) else {
                    resolved = false;
                    break;
                };
                premises.entry(module).or_default().extend(group.names);
            }
            if resolved {
                answer.insert(theorem, premises);
            }
        }
        Some(answer)
    }

    // An interrupted write can only leave an ignored temporary file. All I/O is
    // optional: cache failure never changes a successful verification outcome.
    pub(crate) fn save(&self, record: &DiskRecord) {
        if !self.writable {
            return;
        }
        if !self.directory.exists() && fs::create_dir(&self.directory).is_err() {
            return;
        }
        if !self.directory_is_safe() {
            return;
        }
        let mut normalized = record.clone();
        let bytes = match record_bytes(&normalized) {
            Some(bytes) => bytes,
            None => {
                // Optional oversized advice must not discard valid result caching.
                normalized.hints.clear();
                let Some(bytes) = record_bytes(&normalized) else {
                    return;
                };
                bytes
            }
        };
        if self.read(&normalized.module).as_ref() == Some(&normalized) {
            return;
        }
        let temp = self.directory.join(format!(
            ".{}-{}.tmp",
            std::process::id(),
            NEXT_TEMP.fetch_add(1, Ordering::Relaxed)
        ));
        let Ok(mut file) = OpenOptions::new().write(true).create_new(true).open(&temp) else {
            return;
        };
        let result = (|| -> std::io::Result<()> {
            file.write_all(&bytes)?;
            file.sync_all()?;
            fs::rename(&temp, self.filename(&normalized.module))?;
            Ok(())
        })();
        if result.is_err() {
            let _ = fs::remove_file(temp);
        }
    }
}

// Typed framing prevents ambiguous concatenation. Every embedded module ID is
// replaced with its canonical descriptor, including phantom actuals and binders.
struct PolicyHasher<'a, F: Fn(ModuleId) -> Option<ModuleRef>> {
    hash: Sha256,
    resolve: &'a F,
}

impl<F: Fn(ModuleId) -> Option<ModuleRef>> PolicyHasher<'_, F> {
    fn tag(&mut self, tag: u8) {
        self.hash.update([tag]);
    }
    fn number(&mut self, value: u64) {
        self.hash.update(value.to_le_bytes());
    }
    fn text(&mut self, value: &str) {
        frame(&mut self.hash, value.as_bytes());
    }
    fn module(&mut self, id: ModuleId) -> Option<()> {
        if id < FIRST_NORMAL {
            self.tag(0);
            self.number(id as u64);
        } else {
            self.tag(1);
            self.hash.update(module_identity(&(self.resolve)(id)?)?);
        }
        Some(())
    }
    fn types(&mut self, types: &[AcornType]) -> Option<()> {
        self.number(types.len() as u64);
        for ty in types {
            self.ty(ty)?;
        }
        Some(())
    }
    fn ty(&mut self, ty: &AcornType) -> Option<()> {
        match ty {
            AcornType::Empty => self.tag(0),
            AcornType::Bool => self.tag(1),
            AcornType::Data(module, name, actuals) => {
                self.tag(2);
                self.module(*module)?;
                self.text(name);
                self.types(actuals)?;
            }
            AcornType::Function(function) => {
                self.tag(3);
                self.types(&function.arg_types)?;
                self.ty(&function.return_type)?;
            }
            AcornType::Variable(name, class) | AcornType::Arbitrary(name, class) => {
                self.tag(if matches!(ty, AcornType::Variable(..)) {
                    4
                } else {
                    5
                });
                self.text(name);
                match class {
                    None => self.tag(0),
                    Some(class) => {
                        self.tag(1);
                        self.module(class.module_id)?;
                        self.text(&class.name);
                    }
                }
            }
        }
        Some(())
    }
    fn value(&mut self, value: &AcornValue) -> Option<()> {
        match value {
            AcornValue::Variable(index, ty) => {
                self.tag(0);
                self.number(*index as u64);
                self.ty(ty)?;
            }
            AcornValue::Application(application) => {
                self.tag(1);
                self.value(&application.function)?;
                self.number(application.args.len() as u64);
                for arg in &application.args {
                    self.value(arg)?;
                }
            }
            AcornValue::Lambda(types, body)
            | AcornValue::ForAll(types, body)
            | AcornValue::Exists(types, body) => {
                self.tag(match value {
                    AcornValue::Lambda(..) => 2,
                    AcornValue::ForAll(..) => 3,
                    _ => 4,
                });
                self.types(types)?;
                self.value(body)?;
            }
            AcornValue::Binary(op, left, right) => {
                self.tag(5);
                self.tag(match op {
                    BinaryOp::Implies => 0,
                    BinaryOp::Equals => 1,
                    BinaryOp::NotEquals => 2,
                    BinaryOp::And => 3,
                    BinaryOp::Or => 4,
                });
                self.value(left)?;
                self.value(right)?;
            }
            AcornValue::Not(value) => {
                self.tag(6);
                self.value(value)?;
            }
            AcornValue::Constant(constant) => {
                self.tag(7);
                self.module(constant.module_id)?;
                self.text(&constant.name);
                self.types(&constant.params)?;
                self.ty(&constant.instance_type)?;
            }
            AcornValue::Bool(value) => {
                self.tag(8);
                self.tag(u8::from(*value));
            }
            AcornValue::IfThenElse(condition, yes, no) => {
                self.tag(9);
                self.value(condition)?;
                self.value(yes)?;
                self.value(no)?;
            }
            AcornValue::Match(value, cases) => {
                self.tag(10);
                self.value(value)?;
                self.number(cases.len() as u64);
                for (types, pattern, result) in cases {
                    self.types(types)?;
                    self.value(pattern)?;
                    self.value(result)?;
                }
            }
        }
        Some(())
    }
}

fn goal_policy(
    goals: &[GoalContext],
    resolve: &impl Fn(ModuleId) -> Option<ModuleRef>,
) -> Option<[u8; 32]> {
    let mut state = PolicyHasher {
        hash: Sha256::new(),
        resolve,
    };
    state.text("venticorn:goal-policy:v1");
    state.number(goals.len() as u64);
    for goal in goals {
        state.tag(u8::from(matches!(goal.goal, Goal::Prove(_))));
        state.value(goal.goal.value())?;
        let range = goal.goal.range();
        for value in [
            range.start.line,
            range.start.character,
            range.end.line,
            range.end.character,
            goal.first_line,
            goal.last_line,
            goal.cache_last_line,
        ] {
            state.number(value as u64);
        }
        state.tag(u8::from(goal.inconsistency_okay));
    }
    Some(state.hash.finalize().into())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::acorn_type::TypeClass;
    use crate::acorn_value::ConstantInstance;
    use crate::project::Project;

    fn value_digest(value: &AcornValue, id: ModuleId) -> [u8; 32] {
        let resolve = |module| (module == id).then(|| ModuleRef::Name("canonical.types".into()));
        let mut state = PolicyHasher {
            hash: Sha256::new(),
            resolve: &resolve,
        };
        state.value(value).unwrap();
        state.hash.finalize().into()
    }

    fn annotated_value(id: ModuleId) -> AcornValue {
        let ty = AcornType::Data(
            id,
            "Box".into(),
            vec![AcornType::Variable(
                "T".into(),
                Some(TypeClass {
                    module_id: id,
                    name: "Order".into(),
                }),
            )],
        );
        let arbitrary = AcornType::Arbitrary(
            "U".into(),
            Some(TypeClass {
                module_id: id,
                name: "Order".into(),
            }),
        );
        let constant = AcornValue::Constant(ConstantInstance {
            module_id: id,
            name: "Box.choose".into(),
            params: vec![ty.clone(), arbitrary.clone()],
            instance_type: AcornType::new_functional(vec![arbitrary.clone()], ty.clone()),
        });
        AcornValue::Match(
            Box::new(constant.clone()),
            vec![(
                vec![ty.clone(), arbitrary],
                AcornValue::Variable(0, ty.clone()),
                AcornValue::ForAll(vec![ty], Box::new(constant)),
            )],
        )
    }

    #[test]
    fn canonical_policy_covers_nested_actuals_constraints_effective_types_and_match_binders() {
        let first = annotated_value(2);
        let second = annotated_value(9);
        assert_eq!(value_digest(&first, 2), value_digest(&second, 9));
        let mut changed = first.clone();
        if let AcornValue::Match(_, cases) = &mut changed {
            cases[0].0[0] = AcornType::Bool;
        }
        assert_ne!(value_digest(&first, 2), value_digest(&changed, 2));
        let mut changed = first.clone();
        if let AcornValue::Match(value, _) = &mut changed {
            if let AcornValue::Constant(constant) = value.as_mut() {
                constant.params.swap(0, 1);
            }
        }
        assert_ne!(value_digest(&first, 2), value_digest(&changed, 2));
        let mut changed = first.clone();
        if let AcornValue::Match(value, _) = &mut changed {
            if let AcornValue::Constant(constant) = value.as_mut() {
                constant.instance_type = AcornType::Bool;
            }
        }
        assert_ne!(value_digest(&first, 2), value_digest(&changed, 2));
        let resolve = |_| None;
        let mut state = PolicyHasher {
            hash: Sha256::new(),
            resolve: &resolve,
        };
        assert!(state.value(&first).is_none());
    }

    #[test]
    fn canonical_goal_policy_includes_proof_kind_ranges_and_inconsistency_permission() {
        let mut project = Project::new_mock();
        project.mock("/mock/main.ac", "theorem goal { true }");
        let env = project
            .get_env_by_ref(&ModuleRef::Name("main".into()))
            .unwrap();
        let goal = env.iter_goals().next().unwrap().goal_context().unwrap();
        let resolve = |_| Some(ModuleRef::Name("main".into()));
        let original = goal_policy(std::slice::from_ref(&goal), &resolve).unwrap();
        for field in 0..4 {
            let mut changed = env.iter_goals().next().unwrap().goal_context().unwrap();
            match field {
                0 => changed.inconsistency_okay = !changed.inconsistency_okay,
                1 => changed.cache_last_line += 1,
                2 => changed.last_line += 1,
                _ => changed.goal = Goal::Solve(changed.goal.value().clone(), changed.goal.range()),
            }
            assert_ne!(original, goal_policy(&[changed], &resolve).unwrap());
        }
        assert_ne!(original, goal_policy(&[], &resolve).unwrap());
    }

    #[test]
    fn compiled_identity_is_a_content_digest_with_an_explicit_scoring_policy() {
        let identity = checker_identity();
        let (digest, policy) = identity.split_once(':').unwrap();
        assert_eq!(digest.len(), 64);
        assert!(digest.bytes().all(|byte| byte.is_ascii_hexdigit()));
        assert_eq!(
            policy,
            if cfg!(feature = "onnx") {
                "onnx-with-heuristic-fallback"
            } else {
                "heuristic-only"
            }
        );
    }
    #[test]
    fn advisory_payload_changes_do_not_change_success_identity_or_skip_writes() {
        let root = std::env::temp_dir().join(format!(
            "venticorn_hint_record_{}_{}",
            std::process::id(),
            NEXT_TEMP.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&root).unwrap();
        let storage = PersistentCache::new(&root, true).unwrap();
        let module = ModuleRef::Name("main".into());
        let identity = DiskRecord {
            schema: SCHEMA,
            checker: checker_identity(),
            root: storage.root,
            module: module_identity(&module).unwrap(),
            source: [1; 32],
            dependencies: [2; 32],
            goal_policy: [3; 32],
            hints: BTreeMap::new(),
        };
        let make = |name: &str| {
            identity.clone().with_premises(&BTreeMap::from([(
                "goal".into(),
                PremiseSet::from([(module.clone(), BTreeSet::from([name.into()]))]),
            )]))
        };
        let old = make("old");
        storage.save(&old);
        assert!(storage.matches(&identity));
        let new = make("new");
        storage.save(&new);
        assert_eq!(storage.read(&identity.module), Some(new.clone()));
        let path = storage.filename(&identity.module);
        let modified = fs::metadata(&path).unwrap().modified().unwrap();
        storage.save(&new);
        assert_eq!(fs::metadata(&path).unwrap().modified().unwrap(), modified);
        let mut stale = new.clone();
        stale.source = [9; 32];
        stale.dependencies = [8; 32];
        storage.save(&stale);
        assert!(!storage.matches(&identity));
        assert_eq!(
            storage
                .advisory_premises(&module, |id| (id == &HintModule::Name("main".into()))
                    .then(|| module.clone()))
                .unwrap()["goal"][&module],
            BTreeSet::from(["new".into()])
        );
        // Empty-module theorem entries still obey the early allocation estimate.
        let huge = identity.clone().with_premises(&BTreeMap::from([(
            "x".repeat(MAX_RECORD_BYTES as usize),
            PremiseSet::new(),
        )]));
        assert!(huge.hints.is_empty());
        // Escaping can exceed the byte bound even when the raw estimate fits.
        let oversized = make(&"\n".repeat(8_000));
        assert!(!oversized.hints.is_empty());
        storage.save(&oversized);
        assert!(storage.matches(&identity));
        assert!(storage.read(&identity.module).unwrap().hints.is_empty());
        assert!(fs::metadata(&path).unwrap().len() <= MAX_RECORD_BYTES);
        assert_eq!(
            fs::read_dir(root.join(".venticorn-cache")).unwrap().count(),
            1
        );
        fs::remove_dir_all(root).unwrap();
    }
}
