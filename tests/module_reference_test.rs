use std::path::PathBuf;
use std::time::Duration;

use venticorn::builder::Builder;
use venticorn::module::ModuleRef;
use venticorn::project::Project;
use venticorn::prover::{Outcome, Prover};

#[test]
fn diagnostics_preserve_file_identity_for_success_and_warning() {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", "theorem impossible { false }");
    let environment = project
        .get_env_by_ref(&ModuleRef::from_name("main"))
        .unwrap();
    let goal = environment
        .iter_goals()
        .next()
        .unwrap()
        .goal_context()
        .unwrap();
    let prover = Prover::new(&project, false);
    let file = ModuleRef::File(PathBuf::from("/outside/proof.ac"));
    let mut events = Vec::new();
    {
        let mut builder = Builder::new(|event| events.push(event));
        builder.module_proving_started(&file);
        builder.module_proving_complete(&file);
        builder.module_proving_started(&file);
        builder.search_finished(&prover, &goal, Outcome::Exhausted, Duration::ZERO);
        builder.module_proving_complete(&file);
    }
    let diagnostics: Vec<_> = events
        .into_iter()
        .filter_map(|event| event.diagnostic)
        .collect();
    assert_eq!(diagnostics.len(), 2);
    assert_eq!(diagnostics[0].0, file);
    assert!(diagnostics[0].1.is_none());
    assert_eq!(diagnostics[1].0, file);
    assert!(diagnostics[1].1.is_some());
}
