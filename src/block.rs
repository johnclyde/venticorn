// Modified for Venticorn.

use std::borrow::Cow;
use std::collections::HashMap;
use std::fmt;

use tower_lsp::lsp_types::Range;

use crate::acorn_type::{AcornType, TypeParam};
use crate::acorn_value::{AcornValue, BinaryOp};
use crate::atom::AtomId;
use crate::compilation::{self, ErrorSource};
use crate::constant_name::LocalConstantName;
use crate::environment::{Environment, LineType};
use crate::fact::Fact;
use crate::goal::{Goal, GoalContext};
use crate::project::{ImportFilter, Project};
use crate::proof_step::Truthiness;
use crate::proposition::Proposition;
use crate::statement::Body;
use crate::token::Token;

// Proofs are structured into blocks.
// The environment specific to this block can have a bunch of propositions that need to be
// proved, along with helper statements to express those propositions, but they are not
// visible to the outside world.
pub struct Block {
    // Scope before entering any child; the containing goal uses the final block scope.
    proof_scope: crate::proof_scope::ProofScope,
    // The generic types that this block is polymorphic over.
    // Internally to the block, these are fixed arbitrary types.
    // Externally, these are generic data types.
    type_params: Vec<String>,

    // The arguments to this block, from forall or theorem parameters.
    // Pattern variables are constrained by their match case and are stored separately.
    // Internally to the block, the arguments are constants.
    // Externally, these arguments are variables.
    args: Vec<(String, AcornType)>,

    // A block can have an explicit goal that must be proved.
    // The goal for a block is relative to its internal environment.
    // Everything in the block can be used to achieve this goal.
    // Without an explicit goal, the block still exports the conclusion determined by its code.
    pub goal: Option<Goal>,

    // The environment created inside the block.
    pub env: Environment,
}

// The different ways to construct a block
pub enum BlockParams<'a> {
    // (theorem name, theorem range, premise, goal)
    //
    // The premise and goal are unbound, to be proved based on the args of the theorem.
    //
    // The theorem should already be defined by this name in the external environment.
    // It is either a bool, or a function from something -> bool.
    // The meaning of the theorem is that it is true for all args.
    //
    // The premise is optional.
    Theorem(
        Option<&'a str>,
        Range,
        Option<(AcornValue, Range)>,
        AcornValue,
    ),

    // The assumption to be used by the block, and the range of this assumption.
    Conditional(&'a AcornValue, Range),

    // The expression to solve for, and the range of the "solve <target>" component.
    Solve(AcornValue, Range),

    // (unbound goal, function return type, range of condition)
    // This goal has one more unbound variable than the block args account for.
    // The last one, we are trying to prove there exists a variable that satisfies the goal.
    FunctionSatisfy(AcornValue, AcornType, Range),

    // MatchCase represents a single case within a match statement.
    // The scrutinee, constructor, pattern arguments, and source range of the pattern.
    MatchCase(AcornValue, AcornValue, Vec<(String, AcornType)>, Range),

    // The value is the boolean existence condition that we must prove is true, in order
    // for the constraint to express an inhabited type.
    // The range is of the constraint portion of the statement.
    Constraint(AcornValue, Range),

    // A concrete instance must establish every lowered class condition. The
    // caller has already denied the instance's own membership in the parent
    // environment, before this block and any of its children are constructed.
    // The goal itself is never introduced as a premise or identity definition.
    Instance(AcornValue, Range),

    // No special params needed
    ForAll,
    Problem,
}

impl Block {
    pub fn entry_scope(&self) -> &crate::proof_scope::ProofScope {
        &self.proof_scope
    }

    pub fn new(
        project: &mut Project,
        env: &Environment,
        type_params: Vec<TypeParam>,
        args: Vec<(String, AcornType)>,
        params: BlockParams,
        first_line: u32,
        last_line: u32,
        body: Option<&Body>,
    ) -> compilation::Result<Block> {
        let mut subenv = env.child(first_line, body.is_none());

        // Inside the block, each declared type parameter is fixed but arbitrary.
        let param_pairs: Vec<(String, AcornType)> = type_params
            .iter()
            .map(|param| {
                (
                    param.name.clone(),
                    subenv.bindings.add_arbitrary_type_param(param.clone()),
                )
            })
            .collect();

        // Inside the block, the arguments are constants. Keep values only for
        // goal kinds that bind them, rather than cloning every local declaration.
        let needs_internal_args = matches!(
            &params,
            BlockParams::Theorem(..) | BlockParams::FunctionSatisfy(..)
        );
        let mut internal_args = Vec::new();
        for (arg_name, generic_arg_type) in &args {
            let specific_arg_type = generic_arg_type.instantiate(&param_pairs);
            let name = LocalConstantName::unqualified(arg_name);
            if needs_internal_args {
                let value =
                    subenv
                        .bindings
                        .add_constant_value(name, vec![], specific_arg_type, None, None);
                internal_args.push(
                    value
                        .resolved()
                        .expect("block arguments have no type parameters"),
                );
            } else {
                subenv
                    .bindings
                    .add_constant_named(name, vec![], specific_arg_type, None, None);
            }
        }

        // A theorem's bound goal belongs to its proof scope. Existential and
        // instance/constraint obligations are declared in the containing scope.
        let goal_depth = if matches!(&params, BlockParams::Theorem(..)) {
            subenv.depth
        } else {
            env.depth
        };
        let mut goal = match params {
            BlockParams::Conditional(condition, range) => {
                subenv.push_node(Node::structural(
                    project,
                    &subenv,
                    Proposition::premise(condition.clone(), env.module_id, range),
                ));
                None
            }
            BlockParams::Theorem(theorem_name, theorem_range, premise, unbound_goal) => {
                if let Some(name) = theorem_name {
                    // Within the theorem block, the theorem is treated like a function,
                    // with propositions to define its identity.
                    // This makes it less annoying to define inductive hypotheses.
                    subenv.add_identity_props_named(project, &LocalConstantName::unqualified(name));
                }

                if let Some((unbound_premise, premise_range)) = premise {
                    // Add the premise to the environment, when proving the theorem.
                    // The premise is unbound, so we need to bind the block's arg values.
                    let bound =
                        unbound_premise
                            .instantiate(&param_pairs)
                            .bind_values(0, 0, &internal_args);

                    subenv.push_node(Node::structural(
                        project,
                        &subenv,
                        Proposition::premise(bound, env.module_id, premise_range),
                    ));
                }

                // We can prove the goal either in bound or in function form
                let bound_goal =
                    unbound_goal
                        .instantiate(&param_pairs)
                        .bind_values(0, 0, &internal_args);
                Some(Goal::Prove(Proposition::theorem(
                    false,
                    bound_goal,
                    env.module_id,
                    theorem_range,
                    theorem_name.map(|s| s.to_string()),
                )))
            }
            BlockParams::FunctionSatisfy(unbound_goal, return_type, range) => {
                // In the block, we need to prove this goal in bound form, so bind args to it.
                // The partial goal has variables 0..args.len() bound to the block's args,
                // but there is one last variable that needs to be existentially quantified.
                let partial_goal = unbound_goal.bind_values(0, 0, &internal_args);
                let bound_goal = AcornValue::exists(vec![return_type], partial_goal);
                let prop = Proposition::anonymous(bound_goal, env.module_id, range);
                Some(Goal::Prove(prop))
            }
            BlockParams::MatchCase(scrutinee, constructor, pattern_args, range) => {
                // Each pattern variable is a local constant constrained by this case.
                let mut arg_values = vec![];
                for (arg_name, arg_type) in pattern_args {
                    let value = subenv.bindings.add_constant_value(
                        LocalConstantName::unqualified(&arg_name),
                        vec![],
                        arg_type,
                        None,
                        None,
                    );
                    arg_values.push(
                        value
                            .resolved()
                            .expect("pattern arguments have no type parameters"),
                    );
                }
                let applied = AcornValue::apply(constructor, arg_values);
                let equality = AcornValue::equals(scrutinee, applied);
                subenv.push_node(Node::structural(
                    project,
                    &subenv,
                    Proposition::premise(equality, env.module_id, range),
                ));
                None
            }
            BlockParams::Constraint(constraint, range)
            | BlockParams::Instance(constraint, range) => {
                // The condition is a goal only, never an assumed theorem.
                Some(Goal::Prove(Proposition::anonymous(
                    constraint,
                    env.module_id,
                    range,
                )))
            }
            BlockParams::Solve(target, range) => Some(Goal::Solve(target, range)),
            BlockParams::ForAll | BlockParams::Problem => None,
        };

        if let Some(Goal::Prove(proposition)) = &mut goal {
            proposition.source.depth = goal_depth;
        }

        match body {
            Some(body) => {
                subenv.add_line_types(
                    LineType::Opening,
                    first_line,
                    body.left_brace.line_number as u32,
                );
                for s in &body.statements {
                    subenv.add_statement(project, s)?;
                }
                subenv.add_line_types(
                    LineType::Closing,
                    body.right_brace.line_number as u32,
                    body.right_brace.line_number as u32,
                );
            }
            None => {
                // The subenv is an implicit block, so consider all the lines to be "opening".
                subenv.add_line_types(LineType::Opening, first_line, last_line);
            }
        };
        Ok(Block {
            proof_scope: env.bindings.proof_scope().clone(),
            type_params: type_params.into_iter().map(|p| p.name).collect(),
            args,
            env: subenv,
            goal,
        })
    }

    // Convert a boolean value from the block's environment to a value in the outer environment.
    fn externalize_bool(
        &self,
        outer_env: &Environment,
        inner_value: &AcornValue,
    ) -> Result<AcornValue, String> {
        // The constants that were block arguments will export as "forall" variables.
        let mut forall_names: Vec<String> = vec![];
        let mut forall_types: Vec<AcornType> = vec![];
        for (name, t) in &self.args {
            forall_names.push(name.clone());
            forall_types.push(t.clone());
        }

        // Find all unexportable constants
        let mut unexportable: HashMap<String, AcornType> = HashMap::new();
        outer_env
            .bindings
            .find_unknown_local_constants(inner_value, &mut unexportable)?;

        // Unexportable constants that are not arguments export as "exists" variables.
        let mut exists_names = vec![];
        let mut exists_types = vec![];
        for (name, t) in unexportable {
            if forall_names.contains(&name) {
                continue;
            }
            exists_names.push(name);
            exists_types.push(t);
        }

        // Internal variables need to be shifted over
        let shift_amount = (forall_names.len() + exists_names.len()) as AtomId;

        // The forall must be outside the exists, so order stack variables appropriately
        let mut map: HashMap<String, AtomId> = HashMap::new();
        for (i, name) in forall_names
            .into_iter()
            .chain(exists_names.into_iter())
            .enumerate()
        {
            map.insert(name, i as AtomId);
        }

        // Replace all of the constants that only exist in the inside environment
        let replaced = inner_value.clone().insert_stack(0, shift_amount);
        let replaced = replaced.replace_constants(0, &|c, _depth| {
            // These variables already refer to the enclosing exported quantifiers.
            if c.name.module_id == outer_env.module_id {
                let LocalConstantName::Unqualified(name) = &c.name.local_name else {
                    return None;
                };
                map.get(name)
                    .map(|i| AcornValue::Variable(*i, c.instance_type.clone()))
            } else {
                None
            }
        });
        Ok(
            AcornValue::forall(forall_types, AcornValue::exists(exists_types, replaced))
                .parametrize(self.env.module_id, &self.type_params),
        )
    }

    // Returns a claim usable in the outer environment, and a range where it comes from.
    // Compatibility name for moving a block result into the enclosing scope.
    pub fn export_last_claim(
        &self,
        outer_env: &Environment,
        token: &Token,
    ) -> compilation::Result<(AcornValue, Range)> {
        self.externalize_last_claim(outer_env, token)
    }

    pub fn externalize_last_claim(
        &self,
        outer_env: &Environment,
        token: &Token,
    ) -> compilation::Result<(AcornValue, Range)> {
        let proposition = self
            .env
            .nodes
            .last()
            .and_then(Node::proposition)
            .ok_or_else(|| token.error("expected a claim in this block"))?;
        let (inner_claim, range) = (&proposition.value, proposition.source.range);
        let outer_claim = self
            .externalize_bool(outer_env, inner_claim)
            .map_err(|message| token.error(&message))?;
        Ok((outer_claim, range))
    }

    // Checks if this block solves for the given target.
    // If it does, returns an exported proposition with the solution, and the range where it
    // occurs.
    pub fn solves(
        &self,
        outer_env: &Environment,
        target: &AcornValue,
    ) -> Option<(AcornValue, Range)> {
        let (outer_claim, range) = match self.externalize_last_claim(outer_env, &Token::empty()) {
            Ok((c, r)) => (c, r),
            Err(_) => return None,
        };
        match &outer_claim {
            // We only allow <target> == <solution>, rather than the other way around.
            AcornValue::Binary(BinaryOp::Equals, left, _) => {
                if left.as_ref() == target {
                    Some((outer_claim, range))
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

// Logically, the Environment is arranged like a tree structure.
// There are three types of nodes.
// 1. Structural nodes, that we can assume without proof
// 2. Plain claims, that we need to prove
// 3. Nodes with blocks, where we need to recurse into the block and prove those nodes.
pub struct Node {
    codegen_position: usize,
    // Captured before the declaration enters the enclosing scope.
    proof_scope: crate::proof_scope::ProofScope,
    kind: NodeKind,
}

// Private variants prevent constructing a node without its captured scope.
enum NodeKind {
    Structural(Proposition),
    Claim(Proposition),
    Block(Block, Proposition),
}

impl Node {
    // The declaration's proposition with its effective lexical/contextual role.
    pub fn get_fact(&self) -> Option<Fact> {
        self.get_fact_with_truthiness(self.proposition()?.truthiness())
    }

    pub(crate) fn get_fact_with_truthiness(&self, truthiness: Truthiness) -> Option<Fact> {
        Some(Fact::new(self.proposition()?.clone(), truthiness))
    }

    pub fn is_structural(&self) -> bool {
        matches!(&self.kind, NodeKind::Structural(_))
    }

    pub fn get_block(&self) -> Option<&Block> {
        match &self.kind {
            NodeKind::Block(block, _) => Some(block),
            _ => None,
        }
    }

    // Compatibility accessor for a node's proof block.
    pub fn block(&self) -> Option<&Block> {
        self.get_block()
    }

    #[cfg(test)]
    pub(crate) fn block_mut(&mut self) -> Option<&mut Block> {
        match &mut self.kind {
            NodeKind::Block(block, _) => Some(block),
            _ => None,
        }
    }

    pub fn as_theorem(&self) -> Option<(&str, &AcornValue)> {
        let proposition = self.proposition()?;
        proposition
            .theorem_name()
            .map(|name| (name, &proposition.value))
    }

    pub fn importable(&self) -> bool {
        self.proposition().is_some_and(|p| p.source.importable)
    }

    // Stable premise identity, when this source has one.
    pub fn fact_name(&self) -> Option<String> {
        self.proposition()?.source.fact_name()
    }

    pub fn proposition(&self) -> Option<&Proposition> {
        match &self.kind {
            NodeKind::Structural(proposition)
            | NodeKind::Claim(proposition)
            | NodeKind::Block(_, proposition) => Some(proposition),
        }
    }

    pub fn is_axiom(&self) -> bool {
        self.proposition().is_some_and(|p| p.source.is_axiom())
    }

    pub fn proof_scope(&self) -> &crate::proof_scope::ProofScope {
        &self.proof_scope
    }

    pub fn structural(project: &Project, env: &Environment, proposition: Proposition) -> Self {
        Self::from_parts(project, env, true, proposition, None)
    }

    pub fn claim(project: &Project, env: &Environment, proposition: Proposition) -> Self {
        Self::from_parts(project, env, false, proposition, None)
    }

    pub fn new_block(
        project: &Project,
        env: &Environment,
        block: Block,
        proposition: Proposition,
    ) -> Self {
        Self::from_parts(project, env, false, proposition, Some(block))
    }

    // Compatibility constructor; all paths share expansion and metadata capture.
    pub fn new(
        project: &Project,
        env: &Environment,
        structural: bool,
        proposition: Proposition,
        block: Option<Block>,
    ) -> Self {
        Self::from_parts(project, env, structural, proposition, block)
    }

    fn from_parts(
        project: &Project,
        env: &Environment,
        structural: bool,
        proposition: Proposition,
        block: Option<Block>,
    ) -> Self {
        if structural {
            assert!(block.is_none());
        }
        let mut claim = env.bindings.expand_theorems(project, proposition);
        // A nested declaration stays local even when it has a reusable source name.
        claim.source.importable &= env.top_level;
        claim.source.depth = env.depth;
        Node {
            codegen_position: env.bindings.codegen_position(),
            proof_scope: env.bindings.proof_scope().clone(),
            kind: match block {
                Some(block) => NodeKind::Block(block, claim),
                None if structural => NodeKind::Structural(claim),
                None => NodeKind::Claim(claim),
            },
        }
    }

    pub(crate) fn theorem_name(&self) -> Option<&str> {
        match &self.proposition()?.source.source_type {
            crate::proposition::SourceType::Theorem(name) => name.as_deref(),
            _ => None,
        }
    }

    // All goals in one named declaration contribute to one advisory premise set.
    pub(crate) fn block_name(&self) -> Option<Cow<'_, str>> {
        if let Some(name) = self.theorem_name() {
            return Some(Cow::Borrowed(name));
        }
        match &self.proposition()?.source.source_type {
            crate::proposition::SourceType::ConstantDefinition(_, name) => {
                Some(Cow::Borrowed(name))
            }
            crate::proposition::SourceType::TypeDefinition(name, member) => {
                Some(Cow::Owned(format!("{name}.{member}")))
            }
            crate::proposition::SourceType::Instance(name, class) => {
                Some(Cow::Owned(format!("{name}.instance.{class}")))
            }
            _ => None,
        }
    }

    // Goal traversal is postorder, so every subtree occupies a contiguous slice.
    pub(crate) fn num_goals(&self) -> usize {
        usize::from(self.has_goal())
            + self.get_block().map_or(0, |block| {
                block.env.nodes.iter().map(Node::num_goals).sum::<usize>()
            })
    }

    // Whether this node corresponds to a goal that needs to be proved.
    pub fn has_goal(&self) -> bool {
        if self.is_structural() {
            return false;
        }
        match self.get_block() {
            Some(b) => b.goal.is_some(),
            None => true,
        }
    }
}

// A NodeCursor points at a node. It is used to traverse the nodes in an environment.
#[derive(Clone)]
pub struct NodeCursor<'a> {
    // All the environments that surround this node.
    // (env, index) pairs tell you that the node env.nodes[index] to get to
    // the next environment.
    annotated_path: Vec<(&'a Environment, usize)>,
}

impl fmt::Display for NodeCursor<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.path())
    }
}

impl<'a> NodeCursor<'a> {
    pub fn from_path(env: &'a Environment, path: &[usize]) -> Self {
        assert!(path.len() > 0);
        let mut iter = NodeCursor::new(env, path[0]);
        for &i in &path[1..] {
            iter.descend(i);
        }
        iter
    }

    // Only call this on a module level environment.
    // Returns None if there are no nodes in the environment.
    pub fn new(env: &'a Environment, index: usize) -> Self {
        assert!(env.top_level);
        assert!(env.nodes.len() > index);
        NodeCursor {
            annotated_path: vec![(env, index)],
        }
    }

    pub fn env(&self) -> &'a Environment {
        self.annotated_path.last().unwrap().0
    }

    pub fn node(&self) -> &'a Node {
        let (env, index) = self.annotated_path.last().unwrap();
        &env.nodes[*index]
    }

    // Compatibility accessor for the selected node.
    pub fn current(&self) -> &'a Node {
        self.node()
    }

    pub(crate) fn root_node(&self) -> &Node {
        let (env, index) = self.annotated_path[0];
        &env.nodes[index]
    }

    // All goals below a named top-level theorem contribute to one premise hint.
    pub(crate) fn top_theorem_name(&self) -> Option<&str> {
        let (env, index) = self.annotated_path[0];
        env.nodes[index].theorem_name()
    }

    pub(crate) fn top_block_name(&self) -> Option<Cow<'_, str>> {
        if let Some(name) = self.top_theorem_name() {
            return Some(Cow::Borrowed(name));
        }
        let (env, index) = self.annotated_path[0];
        env.nodes[index].block_name()
    }

    // Can use this as an identifier for the iterator, to compare two of them
    pub fn path(&self) -> Vec<usize> {
        self.annotated_path.iter().map(|(_, i)| *i).collect()
    }

    pub fn num_children(&self) -> usize {
        match self.node().get_block() {
            Some(ref b) => b.env.nodes.len(),
            None => 0,
        }
    }

    // child_index must be less than num_children
    pub fn descend(&mut self, child_index: usize) {
        let new_env = match self.node().get_block() {
            Some(b) => &b.env,
            None => panic!("descend called on a node without a block"),
        };
        assert!(child_index < new_env.nodes.len());
        self.annotated_path.push((new_env, child_index));
    }

    // Whether we can advance to the next sibling, keeping environment the same.
    pub fn has_next(&self) -> bool {
        let (env, index) = self.annotated_path.last().unwrap();
        index + 1 < env.nodes.len()
    }

    // Advances to the next sibling, keeping environment the same.
    pub fn next(&mut self) {
        let (env, index) = self.annotated_path.last_mut().unwrap();
        assert!(*index + 1 < env.nodes.len());
        *index += 1;
    }

    pub fn can_ascend(&self) -> bool {
        self.annotated_path.len() > 1
    }

    pub fn ascend(&mut self) {
        assert!(self.can_ascend());
        self.annotated_path.pop();
    }

    // The fact at the current node.
    pub fn get_fact(&self) -> Option<Fact> {
        let truthiness = if self.env().top_level {
            Truthiness::Factual
        } else {
            Truthiness::Hypothetical
        };
        self.node().get_fact_with_truthiness(truthiness)
    }

    // All facts that can be used to prove the current node.
    // This includes imported facts.
    pub fn usable_facts(&self, project: &Project) -> Vec<Fact> {
        self.usable_facts_filtered(project, None)
    }

    pub fn usable_facts_filtered(
        &self,
        project: &Project,
        filter: Option<&ImportFilter>,
    ) -> Vec<Fact> {
        self.facts_in_scope(project, self.goal_scope(), filter, true)
    }

    pub(crate) fn entry_scope(&self) -> &crate::proof_scope::ProofScope {
        self.node()
            .get_block()
            .map_or(self.node().proof_scope(), |b| b.entry_scope())
    }

    pub fn bindings_for_codegen(&self) -> crate::binding_map::BindingMap {
        match self.node().get_block() {
            Some(block) => block
                .env
                .bindings
                .for_codegen_at(block.env.bindings.codegen_position(), self.goal_scope()),
            None => self
                .env()
                .bindings
                .for_codegen_at(self.node().codegen_position, self.goal_scope()),
        }
    }

    pub fn goal_scope(&self) -> &crate::proof_scope::ProofScope {
        self.node()
            .get_block()
            .map_or(self.node().proof_scope(), |b| b.env.bindings.proof_scope())
    }

    pub(crate) fn local_nodes(&self, include_children: bool) -> Vec<(&Node, Truthiness)> {
        let mut nodes = vec![];
        for (env, index) in &self.annotated_path {
            let truthiness = if env.top_level {
                Truthiness::Factual
            } else {
                Truthiness::Hypothetical
            };
            nodes.extend(env.nodes[..*index].iter().map(|n| (n, truthiness)));
        }
        if include_children {
            if let Some(block) = self.node().get_block() {
                nodes.extend(
                    block
                        .env
                        .nodes
                        .iter()
                        .map(|n| (n, Truthiness::Hypothetical)),
                );
            }
        }
        nodes
    }

    pub(crate) fn facts_in_scope(
        &self,
        project: &Project,
        scope: &crate::proof_scope::ProofScope,
        filter: Option<&ImportFilter>,
        include_children: bool,
    ) -> Vec<Fact> {
        let mut facts = project.imported_facts_in_scope(scope, filter);
        facts.extend(
            self.local_nodes(include_children)
                .into_iter()
                .filter_map(|(node, truthiness)| node.get_fact_with_truthiness(truthiness)),
        );
        facts
    }

    // Get a goal context for the current node.
    pub fn goal_context(&self) -> Result<GoalContext, String> {
        let node = self.node();
        if node.is_structural() {
            return Err(format!(
                "node {} does not need a proof, so it has no goal context",
                self
            ));
        }

        let mut context = if let Some(block) = node.get_block() {
            let goal = match &block.goal {
                Some(goal) => goal,
                None => return Err(format!("block at {} has no goal", self)),
            };
            GoalContext::new(
                &block.env,
                goal.clone(),
                block.env.last_line(),
                block.env.first_line(),
                block.env.last_line(),
            )
        } else {
            let proposition = node
                .proposition()
                .ok_or_else(|| format!("node {} has no proposition", self))?;
            GoalContext::new(
                self.env(),
                Goal::Prove(proposition.clone()),
                proposition.source.range.start.line,
                proposition.source.range.start.line,
                proposition.source.range.end.line,
            )
        };
        if node.get_block().is_none() {
            context.proof_scope = node.proof_scope.clone();
        }
        for (env, _) in &self.annotated_path {
            if !env.top_level {
                context.cache_last_line = context.cache_last_line.max(env.last_line());
            }
        }
        Ok(context)
    }

    // Does a postorder traversal of everything with a goal, at and below this node
    pub fn find_goals(&mut self, output: &mut Vec<NodeCursor<'a>>) {
        for i in 0..self.num_children() {
            self.descend(i);
            self.find_goals(output);
            self.ascend();
        }
        if self.node().has_goal() {
            output.push(self.clone());
        }
    }
}
