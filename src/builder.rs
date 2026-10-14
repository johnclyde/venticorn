// Modified for Venticorn: bounded build identity and explicit diagnostic events.

use std::sync::atomic::{AtomicBool, AtomicU32, Ordering};
use std::time::Duration;

use tower_lsp::lsp_types::{Diagnostic, DiagnosticSeverity};

use crate::build_cache::CachedGoal;
use crate::compilation::Error;
use crate::dataset::Dataset;
use crate::environment::Environment;
use crate::features::Features;
use crate::goal::GoalContext;
use crate::module::{ModuleHash, ModuleRef};
use crate::prover::{Outcome, Prover};

static NEXT_BUILD_ID: AtomicU32 = AtomicU32::new(1);

// A "build" is when we verify a set of goals, determined by a Project.
// For each build, we report many  build events.
#[derive(Debug)]
pub struct BuildEvent {
    // Which build this is an event for.
    pub build_id: u32,

    // Current progress is done / total.
    // This is across all modules.
    pub progress: Option<(i32, i32)>,

    // Human-readable
    pub log_message: Option<String>,

    // The module that the build event is coming from.
    pub module: ModuleRef,

    // Whenever we run into a problem, report a diagnostic.
    pub diagnostic: Option<Diagnostic>,

    // Whenever we verify a goal, report the range of the goal.
    pub verified: Option<(u32, u32)>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BuildStatus {
    // No problems of any kind
    Good,

    // Warnings indicate code that parses okay but can't be verified
    Warning,

    // Errors indicate either the user entered bad code, or we ran into a bug in the build process
    Error,
}

impl BuildStatus {
    pub fn verb(&self) -> &str {
        match self {
            BuildStatus::Good => "succeeded",
            BuildStatus::Warning => "warned",
            BuildStatus::Error => "errored",
        }
    }

    pub fn warn(&mut self) {
        if *self == BuildStatus::Good {
            *self = BuildStatus::Warning;
        }
    }

    pub fn is_error(&self) -> bool {
        match self {
            BuildStatus::Error => true,
            _ => false,
        }
    }

    pub fn is_good(&self) -> bool {
        match self {
            BuildStatus::Good => true,
            _ => false,
        }
    }
}

// State belongs to a module reference, not a numeric ID that can change after reload.
struct ModuleInfo {
    module_ref: ModuleRef,
    direct_dependencies: Vec<ModuleRef>,
    hash: Option<ModuleHash>,
    good: bool,
    expected_goals: Option<usize>,
    goals_started_at: i32,
    verified: Vec<(u32, u32)>,
    goals: Vec<CachedGoal>,
}

// Preserve the existing metadata paths while storage lives in its own module.
pub use crate::build_cache::{BuildCache, CachedModule};

// The Builder exists to manage a single build.
// A single Project can correspond to many builds.
// A single logger is used across all modules.
pub struct Builder<'a> {
    event_handler: Box<dyn FnMut(BuildEvent) + 'a>,

    pub status: BuildStatus,

    // A unique id for each build.
    pub id: u32,

    // The total number of goals to be verified.
    // Counted up during the loading phase.
    pub goals_total: i32,

    // The number of goals handled by a completed search or verified cache entry.
    // This includes both successful and unsuccessful searches.
    pub goals_done: i32,

    // When this flag is set, we emit build events when a goal is slow.
    pub log_when_slow: bool,

    // The current module we are proving. Not set when we are loading.
    current_module: Option<ModuleInfo>,

    old_cache: BuildCache,
    new_cache: Option<BuildCache>,
    cache_ready: bool,

    // If dataset is not None, we are gathering data for training.
    pub dataset: Option<Dataset>,

    // The Builder also tracks statistics.
    // Think of these as having a "goal_done" denominator.

    // Number of goals successfully proven by a fresh search.
    pub num_success: i32,

    // Number of successful goals reused from a completed build.
    pub num_cached: i32,

    // The total number of clauses activated.
    pub num_activated: i32,

    // Total sum of square num_activated.
    pub sum_square_activated: u64,

    // Total number of clauses scored, both active and passive.
    pub num_clauses: i32,

    // The total amount of time spent proving, in seconds.
    pub proving_time: f64,
}

impl<'a> Builder<'a> {
    pub fn new(event_handler: impl FnMut(BuildEvent) + 'a) -> Self {
        Self::with_cache(BuildCache::default(), event_handler)
    }

    pub fn with_cache(cache: BuildCache, event_handler: impl FnMut(BuildEvent) + 'a) -> Self {
        let event_handler = Box::new(event_handler);
        Builder {
            event_handler,
            status: BuildStatus::Good,
            id: NEXT_BUILD_ID
                .fetch_update(
                    std::sync::atomic::Ordering::SeqCst,
                    std::sync::atomic::Ordering::SeqCst,
                    |id| id.checked_add(1),
                )
                .expect("build id exhausted"),
            goals_total: 0,
            goals_done: 0,
            log_when_slow: false,
            current_module: None,
            old_cache: cache,
            new_cache: Some(BuildCache::default()),
            cache_ready: false,
            dataset: None,
            num_success: 0,
            num_cached: 0,
            num_activated: 0,
            sum_square_activated: 0,
            num_clauses: 0,
            proving_time: 0.0,
        }
    }

    fn default_event(&self) -> BuildEvent {
        BuildEvent {
            build_id: self.id,
            progress: None,
            log_message: None,
            module: self.module().clone(),
            diagnostic: None,
            verified: None,
        }
    }

    // Returns Anonymous while loading
    fn module(&self) -> &ModuleRef {
        match self.current_module {
            None => &ModuleRef::Anonymous,
            Some(ref m) => &m.module_ref,
        }
    }

    // Called when a single module is loaded successfully.
    pub fn module_loaded(&mut self, env: &Environment) {
        self.goals_total += env.iter_goals().count() as i32;
    }

    // When create_dataset is called, that tells the Builder to gather data for training.
    // Only call this before the build starts.
    pub fn create_dataset(&mut self) {
        assert_eq!(self.goals_done, 0);
        self.dataset = Some(Dataset::new());
    }

    // Called when the entire loading phase is done.
    pub fn loading_phase_complete(&mut self) {
        let event = BuildEvent {
            progress: Some((0, self.goals_total)),
            ..self.default_event()
        };
        (self.event_handler)(event);
    }

    // Logs an informational message that doesn't change build status.
    pub fn log_info(&mut self, message: String) {
        let event = BuildEvent {
            log_message: Some(message),
            ..self.default_event()
        };
        (self.event_handler)(event);
    }

    // Logs an error during the loading phase, that can be localized to a particular place.
    pub fn log_loading_error(&mut self, module_ref: &ModuleRef, error: &Error) {
        let diagnostic = Diagnostic {
            range: error.range(),
            severity: Some(DiagnosticSeverity::ERROR),
            message: error.to_string(),
            ..Diagnostic::default()
        };
        let event = BuildEvent {
            log_message: Some(format!("fatal error: {}", error)),
            module: module_ref.clone(),
            diagnostic: Some(diagnostic),
            ..self.default_event()
        };
        (self.event_handler)(event);
        self.status = BuildStatus::Error;
    }

    // Called when we start proving a module.
    pub fn module_proving_started(&mut self, module: &ModuleRef) {
        self.module_proving_started_with_metadata(module, Vec::new(), None, None);
    }

    pub(crate) fn module_proving_started_with_metadata(
        &mut self,
        module: &ModuleRef,
        mut direct_dependencies: Vec<ModuleRef>,
        hash: Option<ModuleHash>,
        expected_goals: Option<usize>,
    ) {
        direct_dependencies.sort();
        direct_dependencies.dedup();
        self.current_module = Some(ModuleInfo {
            module_ref: module.clone(),
            direct_dependencies,
            hash,
            good: true,
            expected_goals,
            goals_started_at: self.goals_done,
            verified: Vec::new(),
            goals: Vec::new(),
        });
    }

    pub(crate) fn has_cached_module(
        &self,
        module: &ModuleRef,
        hash: Option<&ModuleHash>,
        expected: &[(u32, u32)],
    ) -> bool {
        self.old_cache.matches(module, hash, expected)
    }

    // Only Project supplies the current parsed ranges and verifies all dependency entries.
    pub(crate) fn handle_current_module_from_cache(
        &mut self,
        goals: &[GoalContext],
        expected: &[(u32, u32)],
        dependencies_verified: bool,
        stopped: &AtomicBool,
    ) -> bool {
        if stopped.load(Ordering::Relaxed) {
            self.interrupted();
            return true;
        }
        if self.dataset.is_some() || !dependencies_verified {
            return false;
        }
        let Some(current) = &self.current_module else {
            return false;
        };
        if goals.len() != expected.len()
            || current.expected_goals != Some(expected.len())
            || !self.has_cached_module(&current.module_ref, current.hash.as_ref(), expected)
        {
            return false;
        }
        for goal in goals {
            if stopped.load(Ordering::Relaxed) {
                self.interrupted();
                return true;
            }
            self.log_proving_success_cached(goal);
        }
        true
    }

    // A partial hit is only available from a fully successful earlier module.
    pub(crate) fn handle_goal_from_cache(
        &mut self,
        goal: &GoalContext,
        dependencies_verified: bool,
        stopped: &AtomicBool,
    ) -> bool {
        if stopped.load(Ordering::Relaxed) {
            self.interrupted();
            return true;
        }
        if self.dataset.is_some() || !dependencies_verified {
            return false;
        }
        let Some(current) = &self.current_module else {
            return false;
        };
        let Some(hash) = &current.hash else {
            return false;
        };
        let index = (self.goals_done - current.goals_started_at) as usize;
        if !self
            .old_cache
            .matches_prefix(&current.module_ref, hash, goal, index)
        {
            return false;
        }
        self.log_proving_success_cached(goal);
        true
    }

    fn log_proving_success_cached(&mut self, goal: &GoalContext) {
        self.goals_done += 1;
        self.num_cached += 1;
        self.record_verified_goal(goal);
        self.log_proving_success(goal.first_line, goal.last_line);
    }

    fn record_verified_goal(&mut self, goal: &GoalContext) {
        if let Some(module) = &mut self.current_module {
            module.verified.push((goal.first_line, goal.last_line));
            module.goals.push(CachedGoal::new(goal));
        }
    }

    fn interrupted(&mut self) {
        self.status = BuildStatus::Error;
        if let Some(module) = &mut self.current_module {
            module.good = false;
        }
        let event = BuildEvent {
            progress: Some((self.goals_total, self.goals_total)),
            log_message: Some("verification was interrupted".into()),
            ..self.default_event()
        };
        (self.event_handler)(event);
    }

    pub fn module_proving_complete(&mut self, module: &ModuleRef) {
        assert_eq!(self.module(), module);
        let info = self.current_module.take().expect("no current module");
        let completed = (self.goals_done - info.goals_started_at) as usize;
        if info.good
            && info.expected_goals == Some(completed)
            && info.verified.len() == completed
            && info.goals.len() == completed
        {
            if let Some(hash) = info.hash {
                if let Some(cache) = &mut self.new_cache {
                    cache.insert_completed(
                        info.module_ref,
                        hash,
                        info.direct_dependencies,
                        info.verified,
                        info.goals,
                    );
                }
            }
        }
    }

    // Cache metadata is only exposed after every target finishes. In particular, a
    // fatal event's display progress is not evidence that proof searches completed.
    pub(crate) fn finish_build(&mut self, completed: bool) {
        self.cache_ready = completed && !self.status.is_error() && self.current_module.is_none();
        if !self.cache_ready {
            self.new_cache = None;
        }
    }

    pub fn cache(&self) -> Option<&BuildCache> {
        if self.cache_ready {
            self.new_cache.as_ref()
        } else {
            None
        }
    }

    // Transfer completed metadata once, while keeping statistics available.
    // Calling this during a build does not consume its unfinished state.
    pub fn take_cache(&mut self) -> Option<BuildCache> {
        if self.cache_ready {
            self.new_cache.take()
        } else {
            None
        }
    }

    pub fn into_cache(mut self) -> Option<BuildCache> {
        self.take_cache()
    }

    // Called when a single proof search completes.
    // Statistics are tracked here.
    pub fn search_finished(
        &mut self,
        prover: &Prover,
        goal_context: &GoalContext,
        outcome: Outcome,
        elapsed: Duration,
    ) {
        // Time conversion
        let secs = elapsed.as_secs() as f64;
        let subsec_nanos = elapsed.subsec_nanos() as f64;
        let elapsed_f64 = secs + subsec_nanos * 1e-9;
        let elapsed_str = format!("{:.3}s", elapsed_f64);

        // Tracking statistics
        self.goals_done += 1;
        self.proving_time += elapsed_f64;
        let num_activated = prover.num_activated() as i32;
        self.num_activated += num_activated;
        let num_passive = prover.num_passive() as i32;
        self.num_clauses += num_activated + num_passive;
        self.sum_square_activated += (num_activated * num_activated) as u64;

        match outcome {
            Outcome::Success => match prover.get_proof() {
                None => self.log_proving_warning(&prover, &goal_context, "had a missing proof"),
                Some(proof) => {
                    if proof.needs_simplification() {
                        self.log_proving_warning(&prover, &goal_context, "needs simplification");
                    } else {
                        // Both of these count as a success.
                        self.num_success += 1;
                        self.record_verified_goal(goal_context);
                        if self.log_when_slow && elapsed_f64 > 0.1 {
                            self.log_proving_info(
                                &prover,
                                &goal_context,
                                &format!("took {}", elapsed_str),
                            );
                        } else {
                            self.log_proving_success(
                                goal_context.first_line,
                                goal_context.last_line,
                            );
                        }
                    }

                    // As long as we have a proof, we can collect data for our dataset.
                    if let Some(ref mut dataset) = self.dataset {
                        for (id, step) in prover.iter_active_steps() {
                            let features = Features::new(step);
                            let label = proof.has_active_id(id);
                            dataset.add(features, label);
                        }
                    }
                }
            },
            Outcome::Exhausted => {
                self.log_proving_warning(&prover, &goal_context, "could not be verified")
            }
            Outcome::Inconsistent => {
                self.log_proving_warning(&prover, &goal_context, "- prover found an inconsistency")
            }
            Outcome::Timeout => self.log_proving_warning(
                &prover,
                &goal_context,
                &format!("timed out after {}", elapsed_str),
            ),
            Outcome::Interrupted => {
                self.log_proving_error(&prover, &goal_context, "was interrupted");
            }
            Outcome::Error => {
                self.log_proving_error(&prover, &goal_context, "had an error");
            }
            Outcome::Constrained => self.log_proving_warning(
                &prover,
                &goal_context,
                "stopped after hitting constraints",
            ),
        }
    }

    // Logs a successful proof.
    fn log_proving_success(&mut self, first_line: u32, last_line: u32) {
        let event = BuildEvent {
            progress: Some((self.goals_done, self.goals_total)),
            verified: Some((first_line, last_line)),
            ..self.default_event()
        };
        (self.event_handler)(event);
    }

    // Create a build event for a proof that was other than successful.
    fn make_event(
        &mut self,
        prover: &Prover,
        goal_context: &GoalContext,
        message: &str,
        sev: DiagnosticSeverity,
    ) -> BuildEvent {
        let mut full_message = format!("{} {}", goal_context.name, message);
        if let Some(e) = &prover.error {
            full_message.push_str(&format!(": {}", e));
        }
        let diagnostic = Diagnostic {
            range: goal_context.goal.range(),
            severity: Some(sev),
            message: full_message.clone(),
            ..Diagnostic::default()
        };
        BuildEvent {
            progress: Some((self.goals_done, self.goals_total)),
            log_message: Some(full_message),
            diagnostic: Some(diagnostic),
            ..self.default_event()
        }
    }

    fn log_proving_info(&mut self, prover: &Prover, goal_context: &GoalContext, message: &str) {
        let mut event = self.make_event(
            prover,
            goal_context,
            message,
            DiagnosticSeverity::INFORMATION,
        );
        event.verified = Some((goal_context.first_line, goal_context.last_line));
        (self.event_handler)(event);
    }

    // Logs a warning. Warnings can only happen during the proving phase.
    fn log_proving_warning(&mut self, prover: &Prover, goal_context: &GoalContext, message: &str) {
        let event = self.make_event(prover, goal_context, message, DiagnosticSeverity::WARNING);
        (self.event_handler)(event);
        if let Some(module) = &mut self.current_module {
            module.good = false;
        }
        self.status.warn();
    }

    // Logs an error during the proving phase.
    fn log_proving_error(&mut self, prover: &Prover, goal_context: &GoalContext, message: &str) {
        let mut event = self.make_event(prover, goal_context, message, DiagnosticSeverity::WARNING);

        // Set progress as complete, because an error will halt the build
        event.progress = Some((self.goals_total, self.goals_total));
        (self.event_handler)(event);
        if let Some(module) = &mut self.current_module {
            module.good = false;
        }
        self.status = BuildStatus::Error;
    }

    pub fn print_stats(&self) {
        println!();
        match self.status {
            BuildStatus::Error => {
                println!("Build failed.");
                return;
            }
            BuildStatus::Warning => {
                println!("Build completed with warnings.");
            }
            BuildStatus::Good => {
                println!("Build completed successfully.");
            }
        }
        let verified = self.num_success + self.num_cached;
        println!("{}/{} OK", verified, self.goals_total);
        let success_percent = if self.goals_total == 0 {
            100.0
        } else {
            100.0 * verified as f64 / self.goals_total as f64
        };
        println!("{:.1}% success rate", success_percent);
        if self.num_cached > 0 {
            println!("{} goals reused from completed builds", self.num_cached);
        }
        if self.num_success == 0 {
            return;
        }
        let num_activated = self.num_activated as f64 / self.num_success as f64;
        println!("{:.2} average activations", num_activated);
        let mean_square_activated = self.sum_square_activated as f64 / self.num_success as f64;
        println!("{:.1} mean square activations", mean_square_activated);
        let num_clauses = self.num_clauses as f64 / self.num_success as f64;
        println!("{:.2} average clauses", num_clauses);
        let proving_time_ms = 1000.0 * self.proving_time / self.num_success as f64;
        println!("{:.1} ms average proving time", proving_time_ms);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::project::Project;

    fn simulate_result(outcome: Outcome, expected_goals: usize) -> Builder<'static> {
        let mut project = Project::new_mock();
        project.mock("/mock/main.ac", "theorem identity { true }");
        let module = ModuleRef::Name("main".into());
        let env = project.get_env_by_ref(&module).unwrap();
        let node = env.iter_goals().next().unwrap();
        let goal = node.goal_context().unwrap();
        let mut prover = Prover::new(&project, false);
        for fact in node.usable_facts(&project) {
            prover.add_fact(fact);
        }
        prover.set_goal(&goal);
        assert_eq!(prover.quick_search(), Outcome::Success);
        let mut builder = Builder::new(|_| {});
        builder.log_when_slow = true;
        builder.module_loaded(env);
        builder.module_proving_started_with_metadata(
            &module,
            Vec::new(),
            project.get_module_hash(env.module_id).cloned(),
            Some(expected_goals),
        );
        builder.search_finished(&prover, &goal, outcome, Duration::from_secs(1));
        builder.module_proving_complete(&module);
        builder.finish_build(true);
        builder
    }

    #[test]
    fn slow_success_keeps_cache_ranges_as_well_as_events() {
        let builder = simulate_result(Outcome::Success, 1);
        let cached = builder
            .cache()
            .unwrap()
            .get(&ModuleRef::Name("main".into()))
            .unwrap();
        assert_eq!(cached.verified(), &[(0, 0)]);
    }

    #[test]
    fn interrupted_or_incomplete_modules_never_enter_the_cache() {
        let interrupted = simulate_result(Outcome::Interrupted, 1);
        assert!(interrupted.cache().is_none());
        let incomplete = simulate_result(Outcome::Success, 2);
        assert_eq!(incomplete.cache().unwrap().num_modules(), 0);
    }
}
