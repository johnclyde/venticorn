// Modified for Venticorn.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::atomic::AtomicBool;
use std::sync::{Arc, Mutex};
use std::{fmt, io};

use sha2::{Digest, Sha256};
use tower_lsp::lsp_types::{CompletionItem, Url};
use walkdir::WalkDir;

use crate::binding_map::BindingMap;
use crate::block::NodeCursor;
use crate::builder::{BuildCache, BuildEvent, BuildStatus, Builder};
use crate::compilation;
use crate::environment::Environment;
use crate::fact::Fact;
use crate::goal::GoalContext;
use crate::module::{Module, ModuleId, ModuleRef, FIRST_NORMAL};
use crate::prover::Prover;
use crate::token::{Token, TokenType};

// A synchronous build's actual proof counts and completed metadata. The cache is
// absent if the build was interrupted or had a fatal error, even if a final event
// displayed complete progress. Only finalized records can seed subsequent verification.
pub struct BuildReport {
    pub status: BuildStatus,
    pub events: Vec<BuildEvent>,
    pub num_success: i32,
    pub num_cached: i32,
    pub goals_done: i32,
    pub goals_total: i32,
    pub cache: Option<BuildCache>,
}

// The Project is responsible for importing different files and assigning them module ids.
pub struct Project {
    // The root directory of the library, used to resolve imports.
    // This may differ from the workspace being edited.
    // Set to "/mock" for mock projects.
    library_root: PathBuf,

    // Whether we permit loading files from the filesystem
    use_filesystem: bool,

    // For "open" files, we use the content we are storing rather than the content on disk.
    // This can store either test data that doesn't exist on the filesystem at all, or
    // work in progress whose state is "owned" by an IDE via the language server protocol.
    //
    // Maps filename -> (contents, version number).
    // The version number can mean whatever the caller wants it to mean.
    // From vscode, it'll be the vscode version number.
    open_files: HashMap<PathBuf, (String, i32)>,

    // Failed or loading modules have no fingerprint. IDs may change after a reload.
    modules: Vec<(ModuleRef, Module, Option<ModuleFingerprint>)>,

    // module_map maps from a module ref to its id
    module_map: HashMap<ModuleRef, ModuleId>,

    // The module references that we want to build.
    targets: HashSet<ModuleRef>,

    // Completed builds publish their staged entries atomically. Searches and callbacks
    // never run with this lock held.
    build_cache: Arc<Mutex<BuildCache>>,

    // Used as a flag to stop a build in progress.
    pub build_stopped: Arc<AtomicBool>,
}

// An error found while importing a module.
// Not an error in the code of the module itself.
#[derive(Debug)]
pub struct LoadError(pub String);

impl From<io::Error> for LoadError {
    fn from(error: io::Error) -> Self {
        LoadError(format!("{}", error))
    }
}

impl fmt::Display for LoadError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

// Fingerprints identify loaded source snapshots; they are not proof certificates.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ModuleFingerprint([u8; 32]);

// Hash lengths and variant tags explicitly; neither map iteration order nor
// transient numeric module IDs participate in logical source identity.
fn logical_fingerprint(
    text: &str,
    mut dependencies: Vec<(&ModuleRef, ModuleFingerprint)>,
) -> ModuleFingerprint {
    fn framed(digest: &mut Sha256, bytes: &[u8]) {
        digest.update((bytes.len() as u64).to_le_bytes());
        digest.update(bytes);
    }
    dependencies.sort_by_key(|(module, _)| *module);
    dependencies.dedup_by_key(|(module, _)| *module);
    let mut digest = Sha256::new();
    digest.update(b"venticorn:module-logic:v1\0");
    framed(&mut digest, text.as_bytes());
    digest.update((dependencies.len() as u64).to_le_bytes());
    for (module, fingerprint) in dependencies {
        match module {
            ModuleRef::Anonymous => digest.update([0]),
            ModuleRef::Name(name) => {
                digest.update([1]);
                framed(&mut digest, name.as_bytes());
            }
            ModuleRef::File(path) => {
                digest.update([2]);
                framed(&mut digest, path.as_os_str().as_encoded_bytes());
            }
        }
        digest.update(fingerprint.0);
    }
    ModuleFingerprint(digest.finalize().into())
}

fn new_modules() -> Vec<(ModuleRef, Module, Option<ModuleFingerprint>)> {
    let mut modules = vec![];
    while modules.len() < FIRST_NORMAL as usize {
        modules.push((ModuleRef::Anonymous, Module::None, None));
    }
    modules
}

fn check_valid_module_part(s: &str, error_name: &str) -> Result<(), LoadError> {
    if s.is_empty() {
        return Err(LoadError(format!("empty module part: {}", error_name)));
    }
    if !s.chars().next().unwrap().is_ascii_lowercase() {
        return Err(LoadError(format!(
            "module parts must start with a lowercase letter: {}",
            error_name
        )));
    }
    for char in s.chars() {
        if !char.is_ascii_alphanumeric() && char != '_' {
            return Err(LoadError(format!(
                "invalid character in module name: '{}' in {}",
                char, error_name
            )));
        }
    }
    Ok(())
}

// Search the working directory and its ancestors, preferring Venticorn's name
// while accepting existing libraries that use the same source format.
fn find_library(start: &Path) -> Option<PathBuf> {
    const NAMES: [&str; 3] = ["venticorn-library", "acornlib", "acorn-library"];
    for directory in start.ancestors() {
        if NAMES
            .iter()
            .any(|name| directory.file_name() == Some(std::ffi::OsStr::new(name)))
        {
            return Some(directory.to_path_buf());
        }
        for name in NAMES {
            let candidate = directory.join(name);
            if candidate.is_dir() {
                return Some(candidate);
            }
        }
    }
    None
}

impl Project {
    // A Project where files are imported from the real filesystem.
    pub fn new(root: &str) -> Project {
        let root = if root.starts_with('/') {
            PathBuf::from(root)
        } else {
            let mut d = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
            d.push(root);
            d
        };
        Self::with_library_root(root)
    }

    fn with_library_root(library_root: PathBuf) -> Project {
        Project {
            library_root,
            use_filesystem: true,
            open_files: HashMap::new(),
            modules: new_modules(),
            module_map: HashMap::new(),
            targets: HashSet::new(),
            build_cache: Arc::new(Mutex::new(BuildCache::default())),
            build_stopped: Arc::new(AtomicBool::new(false)),
        }
    }

    // Resolve a configured library without searching any workspace or working directory.
    pub fn library_override() -> Result<Option<PathBuf>, LoadError> {
        let Some(path) = std::env::var_os("VENTICORN_LIBRARY") else {
            return Ok(None);
        };
        if path.is_empty() {
            return Err(LoadError("VENTICORN_LIBRARY must not be empty".to_string()));
        }
        let path = PathBuf::from(path);
        if !path.is_dir() {
            return Err(LoadError(format!(
                "VENTICORN_LIBRARY is not a directory: {}",
                path.display()
            )));
        }
        Ok(Some(path.canonicalize()?))
    }

    // Discover a library near a real directory without considering process environment.
    pub fn find_local_library(start: &Path) -> Result<Option<PathBuf>, LoadError> {
        let start = start.canonicalize()?;
        if !start.is_dir() {
            return Err(LoadError(format!("not a directory: {}", start.display())));
        }
        find_library(&start)
            .map(|path| path.canonicalize().map_err(LoadError::from))
            .transpose()
    }

    // Construct a filesystem project from an independently selected library root.
    pub fn from_library_root(root: PathBuf) -> Result<Project, LoadError> {
        if !root.is_dir() {
            return Err(LoadError(format!(
                "library is not a directory: {}",
                root.display()
            )));
        }
        Ok(Self::with_library_root(root.canonicalize()?))
    }

    // An explicit library takes precedence. Relative overrides use the process directory.
    pub fn new_from_directory_search(start: &Path) -> Result<Project, LoadError> {
        let root = match Self::library_override()? {
            Some(root) => root,
            None => Self::find_local_library(start)?.ok_or_else(|| {
                LoadError(format!(
                    "no library found from {}; set VENTICORN_LIBRARY to its directory",
                    start.display()
                ))
            })?,
        };
        Self::from_library_root(root)
    }

    // A project discovered from the process working directory.
    pub fn new_local() -> Result<Project, LoadError> {
        Self::new_from_directory_search(Path::new("."))
    }

    // A Project where nothing can be imported.
    pub fn new_mock() -> Project {
        let mut p = Project::new("/mock");
        p.use_filesystem = false;
        p
    }

    // Dropping existing modules lets you update the project for new data.
    // TODO: do this incrementally instead of dropping everything.
    fn drop_modules(&mut self) {
        self.modules = new_modules();
        self.module_map = HashMap::new();
    }

    // You only need read access to an RwLock<Project> to stop the build.
    // When the build is stopped, threads that didn't stop the build themselves should
    // finish any long-running process with an "interrupted" behavior, and give up their
    // locks on the project.
    pub fn stop_build(&self) {
        self.build_stopped
            .store(true, std::sync::atomic::Ordering::Relaxed);
    }

    // You need to have write access to a RwLock<Project> to re-allow the build.
    //
    // To change the project, acquire a read lock, stop the build, acquire a write lock, mess
    // around with the project state however you wanted, then re-allow the build.
    //
    // This asymmetry ensures that when we quickly stop and re-allow the build, any build in
    // progress will in fact stop.
    pub fn allow_build(&mut self) {
        self.build_stopped = Arc::new(AtomicBool::new(false));
    }

    // Returns whether it loaded okay.
    // Either way, it's still added as a target.
    fn add_target_by_ref(&mut self, module_ref: &ModuleRef) -> bool {
        let answer = self.load_module_by_ref(module_ref).is_ok();
        self.targets.insert(module_ref.clone());
        answer
    }

    pub fn add_target_by_name(&mut self, module_name: &str) -> bool {
        self.add_target_by_ref(&ModuleRef::Name(module_name.to_string()))
    }

    // Resolve real files before deciding whether they belong to the library. This
    // keeps relative paths and symlinks identical to imports of the same module.
    pub fn add_target_by_path(&mut self, path: &Path) -> Result<(), LoadError> {
        let canonical;
        let path = if self.use_filesystem {
            canonical = path.canonicalize()?;
            if !canonical.is_file() {
                return Err(LoadError(format!("not a file: {}", path.display())));
            }
            canonical.as_path()
        } else {
            path
        };
        // Legacy projects keep lexical roots and editor overlay keys. Reconcile
        // canonical file targets here without changing editor path identities.
        let canonical_root = if self.use_filesystem && !path.starts_with(&self.library_root) {
            self.library_root.canonicalize().ok()
        } else {
            None
        };
        let root = canonical_root.as_deref().unwrap_or(&self.library_root);
        let module_ref = Self::module_ref_from_path_in_root(path, root)?;
        self.add_target_by_ref(&module_ref);
        Ok(())
    }

    // Adds a target for all files in this directory.
    pub fn add_all_targets(&mut self) -> Result<(), LoadError> {
        if !self.use_filesystem {
            panic!("cannot add all targets without filesystem access")
        }
        // Leave exercises under a problems directory out of verification for now.
        // The project root itself may have any name.
        let entries = WalkDir::new(&self.library_root)
            .into_iter()
            .filter_entry(|entry| {
                entry.depth() == 0 || !entry.file_type().is_dir() || entry.file_name() != "problems"
            });
        for entry in entries {
            let entry = entry.map_err(|error| LoadError(error.to_string()))?;
            if entry.file_type().is_file() {
                let path = entry.path();
                if path.extension() == Some(std::ffi::OsStr::new("ac")) {
                    self.add_target_by_path(path)?;
                }
            }
        }
        Ok(())
    }

    // Whether we currently have this version of a file.
    pub fn has_version(&self, path: &PathBuf, version: i32) -> bool {
        if let Some((_, v)) = self.open_files.get(path) {
            &version == v
        } else {
            false
        }
    }

    // Returns None if we don't have this file at all.
    pub fn get_version(&self, path: &PathBuf) -> Option<i32> {
        self.open_files.get(path).map(|(_, version)| *version)
    }

    // Updating a file makes us treat it as "open". When a file is open, we use the
    // content in memory for it, rather than the content on disk.
    // Updated files are also added as build targets.
    pub fn update_file(
        &mut self,
        path: PathBuf,
        content: &str,
        version: i32,
    ) -> Result<(), LoadError> {
        if self.has_version(&path, version) {
            // No need to do anything
            return Ok(());
        }
        let module_ref = self.module_ref_from_path(&path)?;
        let mut reload_modules = vec![module_ref.clone()];
        // Cached modules may depend on this file, even if its earlier load failed
        // or it is being opened in the editor for the first time.
        // For now, drop everything and reload the targets.
        // TODO: figure out precisely which ones are invalidated.
        self.drop_modules();
        for target in &self.targets {
            reload_modules.push(target.clone());
        }
        self.open_files.insert(path, (content.to_string(), version));
        for module_ref in &reload_modules {
            self.add_target_by_ref(module_ref);
        }
        Ok(())
    }

    pub fn close_file(&mut self, path: PathBuf) -> Result<(), LoadError> {
        if !self.open_files.contains_key(&path) {
            // No need to do anything
            return Ok(());
        }
        let module_ref = self.module_ref_from_path(&path)?;
        self.open_files.remove(&path);
        self.drop_modules();
        self.targets.remove(&module_ref);
        let targets = self.targets.clone();
        for target in targets {
            self.add_target_by_ref(&target);
        }
        Ok(())
    }

    // A read-only snapshot of successful entries from completed builds.
    pub fn cached_build(&self) -> BuildCache {
        self.build_cache.lock().unwrap().clone()
    }

    // Builds all open modules, logging build events.
    // Returns the build status.
    pub fn build(&self, builder: &mut Builder) {
        // Build in alphabetical order by module name for consistency.
        let mut targets = self.targets.iter().collect::<Vec<_>>();
        targets.sort();

        builder.log_info(format!(
            "verifying modules: {}",
            targets
                .iter()
                .map(|target| target.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        ));

        // The first phase is the "loading phase". We load modules and look for errors.
        // If there are errors, we won't try to do proving.
        let mut envs = vec![];
        for target in &targets {
            let module = self.get_module_by_ref(target);
            match module {
                Module::Ok(env) => {
                    builder.module_loaded(&env);
                    envs.push((target, env));
                }
                Module::Error(e) => {
                    if e.secondary {
                        // The real problem is in a different module.
                        // So we don't want to locate the error in this module.
                        builder.log_info(format!("error: {}", e));
                        builder.status = BuildStatus::Error;
                    } else {
                        builder.log_loading_error(target, e);
                    }
                }
                Module::None => {
                    // Targets are supposed to be loaded already.
                    builder.log_info(format!("error: module {} is not loaded", target));
                    builder.status = BuildStatus::Error;
                }
                Module::Loading => {
                    // Happens if there's a circular import. A more localized error should
                    // show up elsewhere, so let's just log.
                    builder.log_info(format!("error: module {} stuck in loading", target));
                    builder.status = BuildStatus::Error;
                }
            }
        }

        if builder.status.is_error() {
            builder.finish_build(false);
            return;
        }

        builder.loading_phase_complete();

        // The second pass is the "proving phase".
        for (target, env) in envs {
            self.verify_target(target, env, builder);
            if builder.status.is_error() {
                builder.finish_build(false);
                return;
            }
        }
        builder.finish_build(
            !self
                .build_stopped
                .load(std::sync::atomic::Ordering::Relaxed)
                && builder.goals_done == builder.goals_total,
        );
        if let Some(completed) = builder.cache() {
            self.build_cache.lock().unwrap().merge_completed(completed);
        }
    }

    // Verifies all goals within this target.
    // Returns the status for this file alone.
    fn verify_target(&self, target: &ModuleRef, env: &Environment, builder: &mut Builder) {
        let dependencies = env
            .bindings
            .direct_dependencies()
            .into_iter()
            .map(|id| self.modules[id as usize].0.clone())
            .collect();
        let ranges = Self::goal_ranges(env);
        builder.module_proving_started_with_metadata(
            target,
            dependencies,
            self.get_hash(env.module_id),
            Some(ranges.len()),
        );
        let dependencies_verified = self.all_dependencies(env.module_id).into_iter().all(|id| {
            let Some(dependency) = self.get_env_by_id(id) else {
                return false;
            };
            builder.has_cached_module(
                &self.modules[id as usize].0,
                self.get_hash(id),
                &Self::goal_ranges(dependency),
            )
        });
        if !builder.handle_current_module_from_cache(
            &ranges,
            dependencies_verified,
            &self.build_stopped,
        ) {
            // Fast and slow modes should be interchangeable here.
            self.for_each_prover_fast(env, &mut |prover, goal_context| {
                self.prove(prover, goal_context, builder)
            });
        }

        builder.module_proving_complete(target);
    }

    fn goal_ranges(env: &Environment) -> Vec<(u32, u32)> {
        env.iter_goals()
            .map(|node| {
                let goal = node.goal_context().expect("no goal context");
                (goal.first_line, goal.last_line)
            })
            .collect()
    }

    // Create a prover for each goal in this environment, and call the callback on it.
    // An error status makes us stop early.
    // Return the combined build status.
    // Slow version that is more simple, for debugging.
    pub fn for_each_prover_slow(
        &self,
        env: &Environment,
        callback: &mut impl FnMut(Prover, GoalContext) -> bool,
    ) {
        for node in env.iter_goals() {
            let goal_context = node.goal_context().expect("no goal context");
            let mut prover = Prover::new(&self, false);
            for fact in node.usable_facts(&self) {
                prover.add_fact(fact);
            }
            prover.set_goal(&goal_context);
            if !callback(prover, goal_context) {
                return;
            }
        }
    }

    // Create a prover for each goal in this environment, and call the callback on it.
    // An error status makes us stop early.
    // Return the combined build status.
    // Fast version that tries to clone prover state rather than rebuilding.
    pub fn for_each_prover_fast(
        &self,
        env: &Environment,
        callback: &mut impl FnMut(Prover, GoalContext) -> bool,
    ) {
        if env.nodes.is_empty() {
            // Nothing to prove
            return;
        }
        let mut prover = Prover::new(&self, false);
        for fact in self.imported_facts(env.module_id) {
            prover.add_fact(fact);
        }
        let mut node = NodeCursor::new(&env, 0);

        while self.for_each_prover_fast_helper(&prover, &mut node, callback) {
            if !node.has_next() {
                break;
            }
            prover.add_fact(node.get_fact());
            node.next();
        }
    }

    // Create a prover for every goal within this node, and call the callback on it.
    // Returns true if we should keep building, false if we should stop.
    // Prover should have all facts loaded before node, but nothing for node itself.
    // This should leave node the same way it found it, although it can mutate it
    // mid-operation.
    // If we return false, node can be left in some unusable state.
    fn for_each_prover_fast_helper(
        &self,
        prover: &Prover,
        node: &mut NodeCursor,
        callback: &mut impl FnMut(Prover, GoalContext) -> bool,
    ) -> bool {
        if node.num_children() == 0 && !node.current().has_goal() {
            // There's nothing to do here
            return true;
        }

        let mut prover = prover.clone();
        if node.num_children() > 0 {
            // We need to recurse into children
            node.descend(0);
            loop {
                if !self.for_each_prover_fast_helper(&prover, node, callback) {
                    return false;
                }

                prover.add_fact(node.get_fact());
                if node.has_next() {
                    node.next();
                } else {
                    break;
                }
            }
            node.ascend();
        }

        if node.current().has_goal() {
            let goal_context = node.goal_context().unwrap();
            prover.set_goal(&goal_context);
            if !callback(prover, goal_context) {
                return false;
            }
        }

        true
    }

    // Proves a single goal in the target, using the provided prover.
    // Reports using the handler as appropriate.
    // Returns true if we should keep building, false if we should stop.
    fn prove(&self, mut prover: Prover, goal_context: GoalContext, builder: &mut Builder) -> bool {
        let start = std::time::Instant::now();
        let outcome = prover.verification_search();

        builder.search_finished(&prover, &goal_context, outcome, start.elapsed());

        !builder.status.is_error()
    }

    // Does the build and returns all events when it's done, rather than asynchronously.
    pub fn sync_build(&self) -> (BuildStatus, Vec<BuildEvent>) {
        let report = self.sync_build_report();
        (report.status, report.events)
    }

    pub fn sync_build_report(&self) -> BuildReport {
        let mut events = vec![];
        let (status, num_success, num_cached, goals_done, goals_total, cache) = {
            let mut builder = Builder::with_cache(self.cached_build(), |event| events.push(event));
            self.build(&mut builder);
            let stats = (
                builder.status,
                builder.num_success,
                builder.num_cached,
                builder.goals_done,
                builder.goals_total,
            );
            (
                stats.0,
                stats.1,
                stats.2,
                stats.3,
                stats.4,
                builder.take_cache(),
            )
        };
        BuildReport {
            status,
            events,
            num_success,
            num_cached,
            goals_done,
            goals_total,
            cache,
        }
    }

    // Set the file content. This has priority over the actual filesystem.
    pub fn mock(&mut self, filename: &str, content: &str) {
        assert!(!self.use_filesystem);
        self.update_file(PathBuf::from(filename), content, 0)
            .expect("mock file update failed");
    }

    pub fn get_hash(&self, module_id: ModuleId) -> Option<ModuleFingerprint> {
        self.modules.get(module_id as usize)?.2
    }

    pub fn get_module_by_id(&self, module_id: ModuleId) -> &Module {
        match self.modules.get(module_id as usize) {
            Some((_, module, _)) => module,
            None => &Module::None,
        }
    }

    pub fn get_module_by_ref(&self, module_ref: &ModuleRef) -> &Module {
        match self.module_map.get(module_ref) {
            Some(id) => self.get_module_by_id(*id),
            None => &Module::None,
        }
    }

    pub fn get_env_by_id(&self, module_id: ModuleId) -> Option<&Environment> {
        if let Module::Ok(env) = self.get_module_by_id(module_id) {
            Some(env)
        } else {
            None
        }
    }

    pub fn get_env_by_ref(&self, module_ref: &ModuleRef) -> Option<&Environment> {
        if let Some(module_id) = self.module_map.get(&module_ref) {
            self.get_env_by_id(*module_id)
        } else {
            None
        }
    }

    pub fn errors(&self) -> Vec<(ModuleId, &compilation::Error)> {
        let mut errors = vec![];
        for (module_id, module) in self.modules.iter().enumerate() {
            if let (_, Module::Error(e), _) = module {
                errors.push((module_id as ModuleId, e));
            }
        }
        errors
    }

    fn read_file(&mut self, path: &PathBuf) -> Result<String, LoadError> {
        if let Some((content, _)) = self.open_files.get(path) {
            return Ok(content.clone());
        }
        if !self.use_filesystem {
            return Err(LoadError(format!("no mocked file for: {}", path.display())));
        }
        match std::fs::read_to_string(&path) {
            Ok(s) => Ok(s),
            Err(e) => Err(LoadError(format!(
                "error loading {}: {}",
                path.display(),
                e
            ))),
        }
    }

    // Returns a load error if this isn't a valid path for an acorn file.
    pub fn module_ref_from_path(&self, path: &Path) -> Result<ModuleRef, LoadError> {
        Self::module_ref_from_path_in_root(path, &self.library_root)
    }

    fn module_ref_from_path_in_root(path: &Path, root: &Path) -> Result<ModuleRef, LoadError> {
        if path.extension() != Some(std::ffi::OsStr::new("ac")) {
            return Err(LoadError(format!(
                "path {} does not end with .ac",
                path.display()
            )));
        }
        let relative = match path.strip_prefix(root) {
            Ok(relative) => relative,
            Err(_) => return Ok(ModuleRef::File(path.to_path_buf())),
        };
        let components: Vec<_> = relative
            .components()
            .map(|comp| comp.as_os_str().to_string_lossy())
            .collect();
        let mut name = String::new();
        for (i, component) in components.iter().enumerate() {
            let part = if i + 1 == components.len() {
                if !component.ends_with(".ac") {
                    return Err(LoadError(format!(
                        "path {} does not end with .ac",
                        path.display()
                    )));
                }
                component[..component.len() - 3].to_string()
            } else {
                component.to_string()
            };
            if i > 0 {
                name.push('.');
            }
            name.push_str(&part);
            check_valid_module_part(&part, &name)?;
        }

        Ok(ModuleRef::Name(name))
    }

    pub fn path_from_module_name(&self, module_name: &str) -> Result<PathBuf, LoadError> {
        let mut path = self.library_root.clone();
        let parts: Vec<&str> = module_name.split('.').collect();

        for (i, part) in parts.iter().enumerate() {
            check_valid_module_part(part, module_name)?;

            let component = if i + 1 == parts.len() {
                format!("{}.ac", part)
            } else {
                part.to_string()
            };
            path.push(component);
        }
        Ok(path)
    }

    pub fn path_from_module_ref(&self, module_ref: &ModuleRef) -> Option<PathBuf> {
        let name = match module_ref {
            ModuleRef::Name(name) => name,
            ModuleRef::File(path) => return Some(path.clone()),
            ModuleRef::Anonymous => return None,
        };

        match self.path_from_module_name(&name) {
            Ok(path) => Some(path),
            Err(_) => None,
        }
    }

    pub fn url_from_module_ref(&self, module_ref: &ModuleRef) -> Option<Url> {
        Url::from_file_path(self.path_from_module_ref(module_ref)?).ok()
    }

    pub fn open_urls(&self) -> impl Iterator<Item = (Url, i32)> + '_ {
        self.open_files.iter().filter_map(|(path, (_, version))| {
            Url::from_file_path(path).ok().map(|url| (url, *version))
        })
    }

    pub fn path_from_module_id(&self, module_id: ModuleId) -> Option<PathBuf> {
        self.path_from_module_ref(&self.modules.get(module_id as usize)?.0)
    }

    // Loads a module from cache if possible, or else from the filesystem.
    // Module names are a .-separated list where each one must be [a-z_].
    // Each component maps to a subdirectory, except the last one, which maps to a .ac file.
    // load returns an error if the module-loading process itself has an error.
    // For example, we might have an invalid name, the file might not exist, or this
    // might be a circular import.
    // If there is an error in the file, the load will return a module id, but the module
    // for the id will have an error.
    // If "open" is passed, then we cache this file's content in open files.
    fn load_module_by_ref(&mut self, module_ref: &ModuleRef) -> Result<ModuleId, LoadError> {
        if let Some(module_id) = self.module_map.get(&module_ref) {
            if *module_id < FIRST_NORMAL {
                panic!("module {} should not be loadable", module_id);
            }
            if let Module::Loading = self.get_module_by_id(*module_id) {
                return Err(LoadError(format!("circular import of {}", module_ref)));
            }
            return Ok(*module_id);
        }

        let path = match self.path_from_module_ref(module_ref) {
            Some(path) => path,
            None => {
                return Err(LoadError(format!(
                    "unloadable module ref: {:?}",
                    module_ref
                )))
            }
        };
        let text = self.read_file(&path)?;

        // Give this module an id before parsing it, so that we can catch circular imports.
        let module_id = self.modules.len() as ModuleId;
        self.modules
            .push((module_ref.clone(), Module::Loading, None));
        self.module_map.insert(module_ref.clone(), module_id);

        let mut env = Environment::new(module_id);
        let tokens = Token::scan(&text);
        let module = if let Err(e) = env.add_tokens(self, tokens) {
            Module::Error(e)
        } else {
            Module::Ok(env)
        };
        let fingerprint = if let Module::Ok(env) = &module {
            // Dependencies are already loaded. Their fingerprints include their own
            // dependencies, so a changed transitive import changes this fingerprint.
            env.bindings
                .direct_dependencies()
                .into_iter()
                .map(|id| Some((&self.modules.get(id as usize)?.0, self.get_hash(id)?)))
                .collect::<Option<Vec<_>>>()
                .map(|deps| logical_fingerprint(&text, deps))
        } else {
            None
        };
        self.modules[module_id as usize].1 = module;
        self.modules[module_id as usize].2 = fingerprint;

        Ok(module_id)
    }

    pub fn load_module_by_name(&mut self, module_name: &str) -> Result<ModuleId, LoadError> {
        let module_ref = ModuleRef::Name(module_name.to_string());
        self.load_module_by_ref(&module_ref)
    }

    // Appends all dependencies, including chains of direct dependencies.
    // Ie, if A imports B and B imports C, then A depends on B and C.
    // The order will be the "pop order", so that each module is added only
    // after all of its dependencies are added.
    pub fn all_dependencies(&self, original_module_id: ModuleId) -> Vec<ModuleId> {
        let mut answer = vec![];
        let mut seen = HashSet::new();
        self.append_dependencies(&mut seen, &mut answer, original_module_id);
        answer
    }

    // Helper function for all_dependencies.
    // Returns "false" if we have already seen this dependency.
    // Does not append module_id itself. If we want it, add that in last.
    fn append_dependencies(
        &self,
        seen: &mut HashSet<ModuleId>,
        output: &mut Vec<ModuleId>,
        module_id: ModuleId,
    ) -> bool {
        if !seen.insert(module_id) {
            return false;
        }
        if let Module::Ok(env) = self.get_module_by_id(module_id) {
            for dep in env.bindings.direct_dependencies() {
                if self.append_dependencies(seen, output, dep) {
                    output.push(dep);
                }
            }
        }
        true
    }

    pub fn get_bindings(&self, module_id: ModuleId) -> Option<&BindingMap> {
        if let Module::Ok(env) = self.get_module_by_id(module_id) {
            Some(&env.bindings)
        } else {
            None
        }
    }

    // All facts that the given module imports.
    pub fn imported_facts(&self, module_id: ModuleId) -> Vec<Fact> {
        let mut facts = vec![];
        for dependency in self.all_dependencies(module_id) {
            let env = self.get_env_by_id(dependency).unwrap();
            facts.extend(env.exported_facts());
        }
        facts
    }

    // Complete against an already evaluated module. Unknown modules have no invented symbols.
    pub fn get_completions(
        &self,
        path: Option<&Path>,
        env_line: u32,
        prefix: &str,
    ) -> Option<Vec<CompletionItem>> {
        // Complete only the token at the cursor, never an earlier word or comment text.
        if prefix.contains("//") || prefix.ends_with(char::is_whitespace) {
            return None;
        }
        let word_start = prefix
            .char_indices()
            .rev()
            .find(|(_, ch)| !Token::identifierish(*ch) && *ch != '.')
            .map_or(0, |(index, ch)| index + ch.len_utf8());
        let word = &prefix[word_start..];
        if word.is_empty() {
            return None;
        }
        let parts: Vec<_> = prefix.split_whitespace().collect();
        if parts.first() == Some(&"from") {
            // Parse the import prefix without loading paths or accepting punctuation as names.
            let tokens = Token::scan(prefix);
            let mut index = 1;
            let mut components = vec![];
            loop {
                let token = tokens.get(index)?;
                if token.token_type != TokenType::Identifier {
                    return None;
                }
                components.push(token.text());
                index += 1;
                match tokens.get(index)?.token_type {
                    TokenType::Dot => index += 1,
                    TokenType::Import => {
                        index += 1;
                        break;
                    }
                    _ => return None,
                }
            }
            loop {
                if tokens.get(index)?.token_type != TokenType::Identifier {
                    return None;
                }
                index += 1;
                match tokens.get(index)?.token_type {
                    TokenType::Comma => index += 1,
                    TokenType::NewLine if index + 1 == tokens.len() => break,
                    _ => return None,
                }
            }
            let module_ref = ModuleRef::Name(components.join("."));
            let env = self.get_env_by_ref(&module_ref)?;
            return env.bindings.get_completions(self, word, true);
        }
        if parts.first() == Some(&"import") {
            // Module-path discovery is separate from completing names within a loaded module.
            return None;
        }
        let module_ref = self.module_ref_from_path(path?).ok()?;
        let env = self.get_env_by_ref(&module_ref)?.env_for_line(env_line);
        env.get_completions(self, env_line, word)
    }

    // Expects the module to load successfully and for there to be no errors in the loaded module.
    // Only for testing.
    pub fn expect_ok(&mut self, module_name: &str) -> ModuleId {
        let module_id = self.load_module_by_name(module_name).expect("load failed");
        match self.get_module_by_id(module_id) {
            Module::Ok(_) => module_id,
            Module::Error(e) => panic!("error in {}: {}", module_name, e),
            _ => panic!("logic error"),
        }
    }

    // This expects there to be an error during loading itself.
    #[cfg(test)]
    fn expect_load_err(&mut self, module_name: &str) {
        assert!(self.load_module_by_name(module_name).is_err());
    }

    // This expects the module to load, but for there to be an error in the loaded module.
    #[cfg(test)]
    fn expect_module_err(&mut self, module_name: &str) {
        let module_id = self.load_module_by_name(module_name).expect("load failed");
        if let Module::Error(_) = self.get_module_by_id(module_id) {
            // What we expected
        } else {
            panic!("expected error");
        }
    }

    // Checks that the given expression can be parsed and turned back into code.
    #[cfg(test)]
    fn check_code_into(&mut self, module_name: &str, input: &str, expected: &str) {
        use crate::expression::Expression;
        let module_id = self.expect_ok(module_name);
        let expression = Expression::expect_value(input);
        let env = self.get_env_by_id(module_id).expect("no env");
        let value = env
            .bindings
            .evaluate_value(self, &expression, None)
            .expect("could not evaluate");
        let output = env
            .bindings
            .value_to_code(&value)
            .expect("could not convert to code");

        if output != expected {
            panic!(
                "\nconverted:\n  {}\nto value:\n  {}\nand back to:\n  {}\nbut expected:\n  {}\n",
                input, value, output, expected
            );
        }
    }

    #[cfg(test)]
    fn check_code(&mut self, module_name: &str, code: &str) {
        self.check_code_into(module_name, code, code);
    }

    #[cfg(test)]
    fn expect_build_ok(&mut self) {
        let (status, events) = self.sync_build();
        assert_eq!(status, BuildStatus::Good);
        assert!(!events.is_empty());
    }

    #[cfg(test)]
    fn expect_build_fails(&mut self) {
        let (status, _) = self.sync_build();
        assert_ne!(status, BuildStatus::Good, "expected build to fail");
    }
}

#[cfg(test)]
mod tests {

    #[test]
    fn invalid_file_updates_and_closes_preserve_existing_state() {
        let mut project = Project::new_mock();
        project.mock("/mock/main.ac", "theorem identity { true }");
        let invalid = PathBuf::from("/outside/not_source.txt");
        assert!(project
            .update_file(invalid.clone(), "theorem identity { true }", 1)
            .is_err());
        assert!(!project.open_files.contains_key(&invalid));
        project
            .open_files
            .insert(invalid.clone(), ("editor content".to_string(), 1));
        assert!(project.close_file(invalid.clone()).is_err());
        assert_eq!(project.open_files[&invalid].0, "editor content");
        assert_eq!(project.sync_build().0, BuildStatus::Good);
    }

    use super::*;

    const FOO_AC: &str = r#"
    // Imported by other tests
    type Foo: axiom
    type AlsoFoo: Foo
    type NotFoo: axiom
    let foo: Foo = axiom
    define fooify(x: Foo) -> Foo { foo }
    "#;

    #[test]
    fn test_named_module_cache_and_path() {
        let mut project = Project::new_mock();
        project.mock("/mock/foo.ac", FOO_AC);
        let first = project.load_module_by_name("foo").unwrap();
        assert_eq!(project.load_module_by_name("foo").unwrap(), first);
        assert!(matches!(
            project.get_module_by_ref(&ModuleRef::Name("foo".to_string())),
            Module::Ok(_)
        ));
        assert_eq!(
            project.path_from_module_id(first),
            Some(PathBuf::from("/mock/foo.ac"))
        );
    }

    #[test]
    fn test_module_references_from_unsaved_paths() {
        let project = Project::new_mock();
        assert_eq!(
            project
                .module_ref_from_path(Path::new("/mock/folder/name.ac"))
                .unwrap(),
            ModuleRef::Name("folder.name".to_string())
        );
        assert_eq!(
            project
                .module_ref_from_path(Path::new("/outside/unsaved.ac"))
                .unwrap(),
            ModuleRef::File(PathBuf::from("/outside/unsaved.ac"))
        );
        for path in [
            "/mock",
            "/mock/file.txt",
            "/outside/file.txt",
            "/mock/invalid-name.ac",
        ] {
            assert!(
                project.module_ref_from_path(Path::new(path)).is_err(),
                "{}",
                path
            );
        }
        assert!(matches!(
            project.get_module_by_ref(&ModuleRef::Anonymous),
            Module::None
        ));
    }

    #[test]
    fn test_reference_paths_and_unknown_module_ids() {
        let project = Project::new_mock();
        assert_eq!(
            project.path_from_module_ref(&ModuleRef::Name("nested.module".to_string())),
            Some(PathBuf::from("/mock/nested/module.ac"))
        );
        let file = PathBuf::from("/outside/unsaved.ac");
        assert_eq!(
            project.path_from_module_ref(&ModuleRef::File(file.clone())),
            Some(file)
        );
        assert_eq!(project.path_from_module_ref(&ModuleRef::Anonymous), None);
        assert_eq!(
            project.path_from_module_ref(&ModuleRef::Name("invalid-name".to_string())),
            None
        );
        assert_eq!(project.path_from_module_id(ModuleId::MAX), None);
    }

    #[test]
    fn test_load_file_reference_and_anonymous_reference() {
        let mut project = Project::new_mock();
        let path = PathBuf::from("/outside/direct.ac");
        project
            .open_files
            .insert(path.clone(), ("theorem identity { true }".to_string(), 1));
        let reference = ModuleRef::File(path.clone());
        let id = project.load_module_by_ref(&reference).unwrap();
        assert_eq!(project.load_module_by_ref(&reference).unwrap(), id);
        assert!(project.get_env_by_ref(&reference).is_some());
        assert_eq!(project.path_from_module_id(id), Some(path));
        assert!(project.load_module_by_ref(&ModuleRef::Anonymous).is_err());
    }

    #[test]
    fn test_basic_import() {
        let mut p = Project::new_mock();
        p.mock("/mock/foo.ac", FOO_AC);
        p.mock("/mock/main.ac", "import foo");
        p.expect_ok("main");
    }

    #[test]
    fn test_direct_import_nonexistent() {
        let mut p = Project::new_mock();
        p.expect_load_err("main");
    }

    #[test]
    fn test_indirect_import_nonexistent() {
        let mut p = Project::new_mock();
        p.mock("/mock/main.ac", "import nonexistent");
        p.expect_module_err("main");
    }

    #[test]
    fn test_nonexistent_property() {
        let mut p = Project::new_mock();
        p.mock("/mock/foo.ac", FOO_AC);
        p.mock(
            "/mock/main.ac",
            r#"
            import foo
            let bar: foo.nonexistent = axiom
        "#,
        );
        p.expect_module_err("main");
    }

    #[test]
    fn test_circular_imports() {
        let mut p = Project::new_mock();
        p.mock("/mock/a.ac", "import b");
        p.mock("/mock/b.ac", "import c");
        p.mock("/mock/c.ac", "import a");
        p.expect_module_err("a");
        // The error should show up in c.ac, not in a.ac
        assert!(p.errors().len() > 0);
    }

    #[test]
    fn test_self_import() {
        let mut p = Project::new_mock();
        p.mock("/mock/a.ac", "import a");
        p.expect_module_err("a");
    }

    #[test]
    fn test_import_from_subdir() {
        let mut p = Project::new_mock();
        p.mock("/mock/stuff/foo.ac", FOO_AC);
        p.mock("/mock/main.ac", "import stuff.foo");
        p.expect_ok("main");
    }

    #[test]
    fn test_good_imported_types() {
        let mut p = Project::new_mock();
        p.mock("/mock/foo.ac", FOO_AC);
        p.mock(
            "/mock/main.ac",
            r#"
            import foo
            type MyFoo: foo.AlsoFoo
            let x: foo.Foo = axiom
            let y: MyFoo = axiom
            let z: Bool = (x = y)
        "#,
        );
        p.expect_ok("main");
    }

    #[test]
    fn test_bad_imported_types() {
        let mut p = Project::new_mock();
        p.mock("/mock/foo.ac", FOO_AC);
        p.mock(
            "/mock/main.ac",
            r#"
            import foo
            type MyFoo: foo.NotFoo
            let x: foo.Foo = axiom
            let y: MyFoo = axiom
            let z: Bool = (x = y)
        "#,
        );
        p.expect_module_err("main");
    }

    #[test]
    fn test_imported_constants() {
        let mut p = Project::new_mock();
        p.mock("/mock/foo.ac", FOO_AC);
        p.mock(
            "/mock/main.ac",
            r#"
            import foo
            let x: foo.Foo = axiom
            let y: foo.Foo = foo.foo
            let z: Bool = (x = y)
        "#,
        );
        p.expect_ok("main");
    }

    #[test]
    fn test_code_generation() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/main.ac",
            r#"
            type MyType: axiom
            let t: MyType = axiom
        "#,
        );
        p.check_code("main", "t");
        p.check_code("main", "forall(x0: MyType) { x0 = t }");
    }

    #[test]
    fn test_code_for_imported_things() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/stuff.ac",
            r#"
            let thing1: Bool = axiom
            let thing2: Bool = axiom
        "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            import stuff
            let st1: Bool = stuff.thing1
        "#,
        );
        p.check_code_into("main", "stuff.thing1", "st1");
        p.check_code("main", "st1");
        p.check_code("main", "stuff.thing2");
    }

    #[test]
    fn test_building_project() {
        let mut p = Project::new_mock();
        p.mock("/mock/foo.ac", FOO_AC);
        p.mock(
            "/mock/main.ac",
            r#"
            import foo
            let new_foo: foo.Foo = axiom
            theorem goal { foo.fooify(new_foo) = foo.foo }
        "#,
        );
        p.load_module_by_name("foo").expect("loading foo failed");
        p.load_module_by_name("main").expect("loading main failed");
        p.add_target_by_name("foo");
        p.add_target_by_name("main");
        p.expect_build_ok();
    }

    #[test]
    fn test_imported_member_functions() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/boolpair.ac",
            r#"
            structure BoolPair {
                first: Bool
                second: Bool
            }
        "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            import boolpair
            type BoolPair: boolpair.BoolPair
            let first: BoolPair -> Bool = BoolPair.first
        "#,
        );
        p.expect_ok("main");
        p.check_code("main", "first");
        p.check_code_into("main", "BoolPair.first", "first");
        p.check_code_into("main", "boolpair.BoolPair.first", "first");

        p.check_code("main", "BoolPair.second");
        p.check_code_into("main", "boolpair.BoolPair.second", "BoolPair.second");
    }

    #[test]
    fn test_structure_aliasing() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/stuff.ac",
            r#"
            structure Foo {
                member: Bool
            }
            type Bar: Foo
        "#,
        );
        p.expect_ok("stuff");
        p.check_code_into("stuff", "Bar.member", "Foo.member");
    }

    #[test]
    fn test_names_imported_via_from() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/stuff.ac",
            r#"
            type Foo: axiom
            class Foo {
                let foo: Bool = true
                let foo2: Bool = false
            }
            type Bar: Foo
            let bar: Bar = axiom
        "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            from stuff import Foo, Bar, bar
            let x: Bool = Bar.foo
            let y: Bar = bar
        "#,
        );
        p.expect_ok("stuff");
        p.expect_ok("main");
        p.check_code("main", "x");
        p.check_code_into("main", "y", "bar");
        p.check_code_into("main", "stuff.Foo.foo2", "Foo.foo2");
    }

    #[test]
    fn test_build_catches_unsolved_solve_blocks() {
        let mut p = Project::new_mock();
        p.mock("/mock/main.ac", "solve false by {\n}");
        p.expect_ok("main");
        p.expect_build_fails();
    }

    #[test]
    fn test_external_target_imports_library_and_builds() {
        let mut project = Project::new_mock();
        project.mock("/mock/foo.ac", FOO_AC);
        let outside_path = PathBuf::from("/outside/proof.ac");
        project
            .update_file(
                outside_path.clone(),
                "import foo\ntheorem identity { foo.foo = foo.foo }",
                1,
            )
            .unwrap();
        let reference = ModuleRef::File(outside_path.clone());
        assert!(project.open_files.contains_key(&outside_path));
        assert!(project.get_env_by_ref(&reference).is_some());
        project.expect_build_ok();
    }

    #[test]
    fn test_imported_numbers_codegen() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/nat.ac",
            r#"
            inductive Nat {
                0
                suc(Nat)
            }

            numerals Nat

            class Nat {
                define add(self, other: Nat) -> Nat {
                    0
                }
            }
        "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            from nat import Nat
            "#,
        );
        p.check_code_into("main", "nat.Nat.0", "Nat.0");
        p.check_code_into("main", "Nat.suc(Nat.0)", "Nat.0.suc");
        p.check_code_into("main", "Nat.add(Nat.0, Nat.0)", "Nat.0 + Nat.0");
    }

    #[test]
    fn test_imported_numbers_codegen_with_numerals() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/nat.ac",
            r#"
            inductive Nat {
                0
                suc(Nat)
            }

            numerals Nat

            class Nat {
                define add(self, other: Nat) -> Nat {
                    0
                }
            }
        "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            from nat import Nat
            numerals Nat
            "#,
        );
        p.check_code_into("main", "nat.Nat.0", "0");
        p.check_code_into("main", "Nat.suc(Nat.0)", "0.suc");
        p.check_code_into("main", "Nat.add(Nat.0, Nat.0)", "0 + 0");
    }

    #[test]
    fn test_prover_iteration_methods() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/nat.ac",
            r#"
            inductive Nat {
                0
                suc(Nat)
            }
            "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            from nat import Nat
            let x: Nat = axiom
            let y: Nat = axiom
            theorem goal(a: Nat) {
                a != x or a != y or x = y
            } by {
                if a = x {
                    if a = y {
                        x = y
                    }
                    a != y or x = y
                }
                a != x or a != y or x = y
            }
            "#,
        );

        let env = p
            .get_env_by_ref(&ModuleRef::Name("main".to_string()))
            .unwrap();

        let mut fast_count = 0;
        let mut slow_count = 0;

        p.for_each_prover_slow(env, &mut |_, _| {
            slow_count += 1;
            true
        });

        p.for_each_prover_fast(env, &mut |_, _| {
            fast_count += 1;
            true
        });

        assert_eq!(fast_count, slow_count);

        // I could test more here. But do I need to?
    }
}

#[cfg(test)]
mod fingerprint_tests {
    use super::*;

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
