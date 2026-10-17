// Modified for Venticorn.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use tower_lsp::lsp_types::{CompletionItem, Range};

use crate::acorn_type::{AcornType, PotentialType, TypeParam, Typeclass};
use crate::acorn_value::{AcornValue, BinaryOp};
use crate::atom::AtomId;
use crate::binding_map::{BindingMap, PotentialValue, Stack, TypeclassCondition, TypeclassInfo};
use crate::block::{Block, BlockParams, Node, NodeCursor};
use crate::compilation::{self, Error, ErrorSource};
use crate::constant_name::LocalConstantName;
use crate::fact::Fact;
use crate::module::ModuleId;
use crate::project::{LoadError, Project};
use crate::proof_step::Truthiness;
use crate::proposition::Proposition;
use crate::statement::{
    Body, ClassStatement, DefineStatement, LetStatement, Statement, StatementInfo,
    TypeclassStatement, VariableSatisfyStatement,
};
use crate::token::{Token, TokenIter, TokenType};

// Each line has a LineType, to handle line-based user interface.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LineType {
    // Only used within subenvironments.
    // The line relates to the block, but is outside the opening brace for this block.
    Opening,

    // This line corresponds to a node inside the environment.
    // The usize is an index into the nodes array.
    // If the node represents a block, this line should also have a line type in the
    // subenvironment within the block.
    Node(usize),

    // Either only whitespace is here, or a comment.
    Empty,

    // Lines with other sorts of statements besides prop statements.
    Other,

    // Only used within subenvironments.
    // The line has the closing brace for this block.
    Closing,
}

// The Environment takes Statements as input and processes them.
// It does not prove anything directly, but it is responsible for determining which
// things need to be proved, and which statements are usable in which proofs.
// It creates subenvironments for nested blocks.
// It does not have to be efficient enough to run in the inner loop of the prover.
pub struct Environment {
    pub module_id: ModuleId,

    // What all the names mean in this environment
    pub bindings: BindingMap,

    // The nodes structure is fundamentally linear.
    // Each node depends only on the nodes before it.
    pub nodes: Vec<Node>,

    // The region in the source document where a name was defined
    definition_ranges: HashMap<String, Range>,

    // Whether a plain "false" is anywhere in this environment.
    // This indicates that the environment is supposed to have contradictory facts.
    pub includes_explicit_false: bool,

    // For the base environment, first_line is zero.
    // first_line is usually nonzero when the environment is a subenvironment.
    // line_types[0] corresponds to first_line in the source document.
    first_line: u32,
    line_types: Vec<LineType>,

    // Implicit blocks aren't written in the code; they are created for theorems that
    // the user has asserted without proof.
    pub implicit: bool,

    // Whether this environment is at the top level of a module.
    pub top_level: bool,
}

impl Environment {
    pub fn new(module_id: ModuleId) -> Self {
        Environment {
            module_id,
            bindings: BindingMap::new(module_id),
            nodes: Vec::new(),
            definition_ranges: HashMap::new(),
            includes_explicit_false: false,
            first_line: 0,
            line_types: Vec::new(),
            implicit: false,
            top_level: true,
        }
    }

    // Create a child environment.
    pub fn child(&self, first_line: u32, implicit: bool) -> Self {
        Environment {
            module_id: self.module_id,
            bindings: self.bindings.clone(),
            nodes: Vec::new(),
            definition_ranges: self.definition_ranges.clone(),
            includes_explicit_false: false,
            first_line,
            line_types: Vec::new(),
            implicit,
            top_level: false,
        }
    }

    fn next_line(&self) -> u32 {
        self.line_types.len() as u32 + self.first_line
    }

    pub fn first_line(&self) -> u32 {
        self.first_line
    }

    pub fn last_line(&self) -> u32 {
        self.next_line() - 1
    }

    // Add line types for the given range, inserting empties as needed.
    // If the line already has a type, do nothing.
    pub fn add_line_types(&mut self, line_type: LineType, first: u32, last: u32) {
        while self.next_line() < first {
            self.line_types.push(LineType::Empty);
        }
        while self.next_line() <= last {
            self.line_types.push(line_type);
        }
    }

    fn add_other_lines(&mut self, statement: &Statement) {
        self.add_line_types(
            LineType::Other,
            statement.first_line(),
            statement.last_line(),
        );
    }

    // Associate a proof node with the source range that selects it.
    fn add_node_lines(&mut self, index: usize, range: &Range) {
        self.add_line_types(LineType::Node(index), range.start.line, range.end.line);
    }

    fn get_line_type(&self, line: u32) -> Option<LineType> {
        if line < self.first_line {
            return None;
        }
        let index = (line - self.first_line) as usize;
        if index < self.line_types.len() {
            Some(self.line_types[index])
        } else {
            None
        }
    }

    // Adds a node to the environment tree.
    // This also macro-expands theorem names into their definitions.
    // Ideally, that would happen during expression parsing.
    // However, it needs to work with templated theorems, which makes it tricky/hacky to do the
    // type inference.
    pub fn add_node(
        &mut self,
        project: &Project,
        structural: bool,
        proposition: Proposition,
        block: Option<Block>,
    ) -> usize {
        let node = Node::new(project, self, structural, proposition, block);
        self.nodes.push(node);
        self.nodes.len() - 1
    }

    // Adds a proposition, or multiple propositions, to represent the definition of the provided
    // constant.
    pub fn add_identity_props(&mut self, project: &Project, name: &str) {
        let definition = if let Some(d) = self.bindings.get_definition(name) {
            d.clone()
        } else {
            return;
        };

        let constant_type_clone = self
            .bindings
            .get_type_for_constant_name(name)
            .unwrap()
            .clone();
        let param_names = self.bindings.get_params(name);

        let params = param_names.into_iter().map(AcornType::Variable).collect();
        let constant = AcornValue::constant(
            self.module_id,
            name.to_string(),
            params,
            constant_type_clone,
        );

        let claim = if let AcornValue::Lambda(acorn_types, return_value) = definition {
            let args: Vec<_> = acorn_types
                .iter()
                .enumerate()
                .map(|(i, acorn_type)| AcornValue::Variable(i as AtomId, acorn_type.clone()))
                .collect();
            let app = AcornValue::apply(constant.clone(), args);
            AcornValue::ForAll(
                acorn_types,
                Box::new(AcornValue::Binary(
                    BinaryOp::Equals,
                    Box::new(app),
                    return_value,
                )),
            )
        } else {
            AcornValue::equals(constant.clone(), definition)
        };
        let range = self.definition_ranges.get(name).unwrap().clone();

        self.add_node(
            project,
            true,
            Proposition::named_constant_definition(
                claim,
                self.module_id,
                range,
                constant,
                name.to_string(),
            ),
            None,
        );
    }

    pub fn get_definition(&self, name: &str) -> Option<&AcornValue> {
        self.bindings.get_definition(name)
    }

    pub fn get_theorem_claim(&self, name: &str) -> Option<AcornValue> {
        for prop in &self.nodes {
            if let Some(claim_name) = prop.claim.theorem_name() {
                if claim_name == name {
                    return Some(prop.claim.value.clone());
                }
            }
        }
        None
    }

    // Find the innermost proof environment containing this saved source line.
    pub fn env_for_line(&self, line: u32) -> &Environment {
        if let Some(LineType::Node(index)) = self.get_line_type(line) {
            if let Some(block) = &self.nodes[index].block {
                // A line following this closing brace belongs to the parent scope.
                if block.env.get_line_type(line) != Some(LineType::Closing) {
                    return block.env.env_for_line(line);
                }
            }
        }
        self
    }

    pub fn get_completions(
        &self,
        project: &Project,
        line: u32,
        prefix: &str,
    ) -> Option<Vec<CompletionItem>> {
        self.bindings
            .get_completions_visible(project, prefix, false, &|name| {
                self.definition_ranges
                    .get(name)
                    .map_or(true, |range| range.start.line <= line)
            })
    }

    // Adds a conditional block to the environment.
    // Takes the condition, the range to associate with the condition, the first line of
    // the conditional block, and finally the body itself.
    // If this is an "else" block, we pass in the claim from the "if" part of the block.
    // This way, if the claim is the same, we can simplify by combining them when exported.
    // Returns the last claim in the block, if we didn't have an if-claim to match against.
    fn add_conditional(
        &mut self,
        project: &mut Project,
        condition: AcornValue,
        range: Range,
        first_line: u32,
        last_line: u32,
        body: &Body,
        if_claim: Option<AcornValue>,
    ) -> compilation::Result<Option<AcornValue>> {
        if body.statements.is_empty() {
            // Conditional blocks with an empty body can just be ignored
            return Ok(None);
        }
        let block = Block::new(
            project,
            &self,
            vec![],
            vec![],
            BlockParams::Conditional(&condition, range),
            first_line,
            last_line,
            Some(body),
        )?;
        let (outer_claim, claim_range) = block.export_last_claim(self, &body.right_brace)?;

        let matching_branches = if let Some(if_claim) = if_claim {
            if outer_claim == if_claim {
                true
            } else {
                false
            }
        } else {
            false
        };
        let (external_claim, last_claim) = if matching_branches {
            (outer_claim, None)
        } else {
            (
                AcornValue::Binary(
                    BinaryOp::Implies,
                    Box::new(condition),
                    Box::new(outer_claim.clone()),
                ),
                Some(outer_claim),
            )
        };
        let index = self.add_node(
            project,
            false,
            Proposition::anonymous(external_claim, self.module_id, claim_range),
            Some(block),
        );
        self.add_line_types(
            LineType::Node(index),
            first_line,
            body.right_brace.line_number,
        );
        Ok(last_claim)
    }

    // Adds a "let" statement to the environment, that may be within a class block.
    fn add_let_statement(
        &mut self,
        project: &Project,
        constant_name: LocalConstantName,
        class_params: &[String],
        ls: &LetStatement,
        range: Range,
    ) -> compilation::Result<()> {
        if !class_params.is_empty() && ls.name_token.token_type == TokenType::Numeral {
            return Err(ls
                .name_token
                .error("numeric literals cannot have type parameters"));
        }
        if !constant_name.is_qualified() && ls.name_token.token_type == TokenType::Numeral {
            return Err(ls
                .name_token
                .error("numeric literals may not be defined outside of a class"));
        }
        if ls.name == "self"
            || ls.name == "new"
            || ls.name == "read"
            || (constant_name.is_qualified()
                && TokenType::from_magic_method_name(&ls.name).is_some())
        {
            return Err(ls.name_token.error(&format!(
                "'{}' is a reserved word. use a different name",
                ls.name
            )));
        }
        let name = constant_name.to_string();
        if self.bindings.constant_name_in_use(&constant_name) {
            return Err(ls.name_token.error(&format!(
                "constant name '{}' already defined in this scope",
                name
            )));
        }
        let acorn_type = self.bindings.evaluate_type(project, &ls.type_expr)?;
        if ls.name_token.token_type == TokenType::Numeral {
            let (class_name, _) = constant_name.as_attribute().ok_or_else(|| {
                ls.name_token
                    .error("numeric literals must be class members")
            })?;
            if acorn_type != AcornType::Data(self.module_id, class_name.to_string(), vec![]) {
                return Err(ls
                    .type_expr
                    .error("numeric class variables must be the class type"));
            }
        }
        let value = if ls.value.is_axiom() {
            None
        } else {
            Some(
                self.bindings
                    .evaluate_value(project, &ls.value, Some(&acorn_type))?,
            )
        };
        if !class_params.is_empty() {
            let constant_type = acorn_type.parametrize(self.module_id, class_params);
            let definition = value.map(|v| v.parametrize(self.module_id, class_params));
            if constant_type.has_arbitrary()
                || definition.as_ref().is_some_and(AcornValue::has_arbitrary)
            {
                return Err(ls
                    .name_token
                    .error("generic member cannot capture arbitrary types"));
            }
            self.bindings.add_constant_named(
                &constant_name,
                self.scoped_type_params(class_params),
                constant_type,
                definition,
                None,
            );
            self.definition_ranges.insert(name.clone(), range);
            self.add_identity_props(project, &name);
            return Ok(());
        }
        if let Some(value) = &value {
            if let Some((canonical_module, canonical_name)) = value.as_simple_constant() {
                // 'let x = y' creates an alias for y, not a new constant.
                self.bindings.add_alias(
                    &name,
                    canonical_module,
                    canonical_name.to_string(),
                    PotentialValue::Resolved(value.clone()),
                );
                self.definition_ranges.insert(name.clone(), range);
                return Ok(());
            }
        }

        self.bindings
            .add_constant_named(&constant_name, vec![], acorn_type, value, None);
        self.definition_ranges.insert(name.clone(), range);
        self.add_identity_props(project, &name);
        Ok(())
    }

    // Adds a "define" statement to the environment, that may be within a class block.
    fn add_define_statement(
        &mut self,
        project: &Project,
        constant_name: LocalConstantName,
        self_type: Option<&AcornType>,
        class_params: &[String],
        ds: &DefineStatement,
        range: Range,
    ) -> compilation::Result<()> {
        if ds.name == "new" || ds.name == "self" {
            return Err(ds.name_token.error(&format!(
                "'{}' is a reserved word. use a different name",
                ds.name
            )));
        }
        if !class_params.is_empty() && !ds.type_params.is_empty() {
            return Err(ds.type_params[0]
                .error("generic class members cannot declare additional type parameters"));
        }
        match self_type {
            Some(AcornType::Data(..)) if constant_name.is_qualified() => {}
            None if !constant_name.is_qualified() => {}
            _ => return Err(ds.name_token.error("class type must be a data type")),
        }
        let name = constant_name.to_string();
        if self.bindings.constant_name_in_use(&constant_name) {
            return Err(ds.name_token.error(&format!(
                "function name '{}' already defined in this scope",
                name
            )));
        }

        if self_type.is_some() && ds.args.is_empty() {
            return Err(ds
                .name_token
                .error("a member function must have a 'self' argument"));
        }

        // Calculate the function value
        let (param_names, _, arg_types, unbound_value, value_type) =
            self.bindings.evaluate_scoped_value_named(
                project,
                &ds.type_params,
                &ds.args,
                Some(&ds.return_type),
                &ds.return_value,
                self_type,
                Some(&constant_name),
            )?;

        if let Some(class_type) = self_type {
            if &arg_types[0] != class_type {
                return Err(ds.args[0].token().error("self must be the class type"));
            }

            if ds.name == "read" {
                if arg_types.len() != 2 || &arg_types[1] != class_type || &value_type != class_type
                {
                    return Err(ds.name_token.error(&format!(
                        "{}.read should be type ({}, {}) -> {}",
                        class_type, class_type, class_type, class_type
                    )));
                }
            }
        }

        let (mut constant_type, mut definition) = match unbound_value {
            Some(value) => {
                let definition = AcornValue::lambda(arg_types, value);
                (definition.get_type(), Some(definition))
            }
            None => (AcornType::functional(arg_types, value_type), None),
        };
        let param_names = if class_params.is_empty() {
            param_names
        } else {
            // Only the class's declared fixed types become generic. Outer proof types
            // must remain fixed and are rejected if this declaration would capture them.
            constant_type = constant_type.parametrize(self.module_id, class_params);
            definition = definition.map(|value| {
                value
                    .parametrize(self.module_id, class_params)
                    .replace_constants(0, &|constant, _| {
                        if constant.module_id == self.module_id
                            && constant.name == name
                            && constant.params.is_empty()
                        {
                            Some(AcornValue::constant(
                                constant.module_id,
                                constant.name.clone(),
                                self.scoped_type_params(class_params)
                                    .into_iter()
                                    .map(AcornType::Variable)
                                    .collect(),
                                constant.instance_type.clone(),
                            ))
                        } else {
                            None
                        }
                    })
            });
            if constant_type.has_arbitrary()
                || definition.as_ref().is_some_and(AcornValue::has_arbitrary)
            {
                return Err(ds
                    .name_token
                    .error("generic member cannot capture arbitrary types"));
            }
            self.scoped_type_params(class_params)
        };
        self.bindings.add_constant_named(
            &constant_name,
            param_names,
            constant_type,
            definition,
            None,
        );

        self.definition_ranges.insert(name.clone(), range);
        self.add_identity_props(project, &name);
        Ok(())
    }

    fn add_theorem_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        ts: &crate::statement::TheoremStatement,
    ) -> compilation::Result<()> {
        if let Some(name) = &ts.name {
            self.bindings
                .check_unqualified_name_available(&statement.first_token, name)?;
        }
        if ts.axiomatic && ts.body.is_some() {
            return Err(statement.error("axioms cannot have proof blocks"));
        }

        // Figure out the range for this theorem definition.
        // It's smaller than the whole theorem statement because it doesn't
        // include the proof block.
        let range = Range {
            start: statement.first_token.start_pos(),
            end: ts.claim_right_brace.end_pos(),
        };

        let (type_params, arg_names, arg_types, value, _) =
            self.bindings.evaluate_scoped_value_named(
                project,
                &ts.type_params,
                &ts.args,
                None,
                &ts.claim,
                None,
                None,
            )?;

        let unbound_claim = value.ok_or_else(|| ts.claim.error("theorems must have values"))?;

        let is_citation = self.bindings.is_citation(project, &unbound_claim);
        if is_citation && ts.body.is_some() {
            return Err(statement.error("citations do not need proof blocks"));
        }

        let mut block_args = vec![];
        for (arg_name, arg_type) in arg_names.iter().zip(&arg_types) {
            block_args.push((arg_name.clone(), arg_type.clone()));
        }

        // Externally we use the theorem in unnamed, "forall" form
        let external_claim = AcornValue::forall(arg_types.clone(), unbound_claim.clone());

        let (premise, goal) = match &unbound_claim {
            AcornValue::Binary(BinaryOp::Implies, left, right) => {
                let premise_range = match ts.claim.premise() {
                    Some(p) => p.range(),
                    None => {
                        // I don't think this should happen, but it's awkward for the
                        // compiler to enforce, so pick a not-too-wrong default.
                        ts.claim.range()
                    }
                };
                (Some((*left.clone(), premise_range)), *right.clone())
            }
            c => (None, c.clone()),
        };

        // Stage only the new binding and range. Existing proof nodes are not cloned.
        // A malformed body must not leave an axiom-like theorem name behind.
        let mut staged = self.child(statement.first_line(), true);
        if let Some(name) = &ts.name {
            if arg_names.contains(name) || type_params.iter().any(|p| &p.name == name) {
                return Err(statement.error("theorem name conflicts with a parameter"));
            }
            let lambda_claim = AcornValue::lambda(arg_types, unbound_claim);
            staged.bindings.add_constant_named(
                &LocalConstantName::unqualified(name),
                type_params.clone(),
                lambda_claim.get_type(),
                Some(lambda_claim),
                None,
            );
            staged.definition_ranges.insert(name.clone(), range);
        }

        let already_proven = ts.axiomatic || is_citation;

        let block = if already_proven {
            None
        } else {
            Some(Block::new(
                project,
                &staged,
                type_params,
                block_args,
                BlockParams::Theorem(ts.name.as_deref(), range, premise, goal),
                statement.first_line(),
                statement.last_line(),
                ts.body.as_ref(),
            )?)
        };

        let node = Node::new(
            project,
            &staged,
            already_proven,
            Proposition::theorem(
                ts.axiomatic,
                external_claim,
                self.module_id,
                range,
                ts.name.clone(),
            ),
            block,
        );
        for param in &ts.type_params {
            if param.typeclass.is_some() && !node.claim.value.has_type_variable(param.name.text()) {
                return Err(
                    param.error("bounded theorem parameter must occur in the exported proposition")
                );
            }
        }
        if let Some(name) = &ts.name {
            self.bindings = staged.bindings;
            self.definition_ranges.insert(name.clone(), range);
        }
        let index = self.nodes.len();
        self.nodes.push(node);
        self.add_node_lines(index, &statement.range());
        if let Some(name) = &ts.name {
            self.bindings.mark_as_theorem(name);
        }

        Ok(())
    }

    fn add_function_satisfy_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        fss: &crate::statement::FunctionSatisfyStatement,
    ) -> compilation::Result<()> {
        if fss.name == "new" || fss.name == "self" {
            return Err(fss.name_token.error(&format!(
                "'{}' is a reserved word. use a different name",
                fss.name
            )));
        }
        self.bindings
            .check_unqualified_name_available(statement, &fss.name)?;

        // Figure out the range for this function definition.
        // It's smaller than the whole function statement because it doesn't
        // include the proof block.
        let definition_range = Range {
            start: statement.first_token.start_pos(),
            end: fss.satisfy_token.end_pos(),
        };
        self.definition_ranges
            .insert(fss.name.clone(), definition_range);

        let (_, mut arg_names, mut arg_types, condition, _) =
            self.bindings.evaluate_scoped_value_named(
                project,
                &[],
                &fss.declarations,
                None,
                &fss.condition,
                None,
                None,
            )?;

        let unbound_condition = condition.ok_or_else(|| statement.error("missing condition"))?;
        if unbound_condition.get_type() != AcornType::Bool {
            return Err(fss.condition.error("condition must be a boolean"));
        }

        // The return variable shouldn't become a block arg, because we're trying to
        // prove its existence.
        let _return_name = arg_names.pop().unwrap();
        let return_type = arg_types.pop().unwrap();
        let block_args: Vec<_> = arg_names
            .iter()
            .cloned()
            .zip(arg_types.iter().cloned())
            .collect();
        let num_args = block_args.len() as AtomId;

        let block = Block::new(
            project,
            &self,
            vec![],
            block_args,
            BlockParams::FunctionSatisfy(
                unbound_condition.clone(),
                return_type.clone(),
                fss.condition.range(),
            ),
            statement.first_line(),
            statement.last_line(),
            fss.body.as_ref(),
        )?;

        // We define this function not with an equality, but via the condition.
        let function_type = AcornType::functional(arg_types.clone(), return_type);
        self.bindings.add_constant_named(
            &LocalConstantName::unqualified(&fss.name),
            vec![],
            function_type.clone(),
            None,
            None,
        );
        let function_constant =
            AcornValue::constant(self.module_id, fss.name.clone(), vec![], function_type);
        let function_term = AcornValue::apply(
            function_constant.clone(),
            arg_types
                .iter()
                .enumerate()
                .map(|(i, t)| AcornValue::Variable(i as AtomId, t.clone()))
                .collect(),
        );
        let return_bound = unbound_condition.bind_values(num_args, num_args, &[function_term]);
        let external_condition = AcornValue::ForAll(arg_types, Box::new(return_bound));

        let prop = Proposition::named_constant_definition(
            external_condition,
            self.module_id,
            definition_range,
            function_constant,
            fss.name.clone(),
        );

        let index = self.add_node(project, false, prop, Some(block));
        self.add_node_lines(index, &statement.range());
        Ok(())
    }

    fn add_structure_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        ss: &crate::statement::StructureStatement,
    ) -> compilation::Result<()> {
        self.bindings
            .check_typename_available(statement, &ss.name)?;

        let formals = self
            .bindings
            .evaluate_type_params(project, &ss.type_params)?;
        if let Some(param) = ss
            .type_params
            .iter()
            .find(|param| param.name.text() == ss.name)
        {
            return Err(param
                .name
                .error("type parameter already defined in this scope"));
        }
        let mut param_names = Vec::with_capacity(formals.len());
        let mut arbitrary_params = Vec::with_capacity(formals.len());
        for param in &formals {
            param_names.push(param.name.clone());
            arbitrary_params.push(self.bindings.add_arbitrary_type_param(param.clone()));
        }

        // Parse the fields before adding the struct type so that we can't have
        // self-referential structs.
        let mut member_fn_names = vec![];
        let mut field_types = vec![];
        for (field_name_token, field_type_expr) in &ss.fields {
            let field_type = self.bindings.evaluate_type(project, &field_type_expr)?;
            field_types.push(field_type.clone());
            if field_name_token.text() == "new"
                || TokenType::from_magic_method_name(field_name_token.text()).is_some()
            {
                return Err(field_name_token.error(&format!(
                    "'{}' is a reserved word. use a different name",
                    field_name_token.text()
                )));
            }
            let member_fn_name = LocalConstantName::attribute(&ss.name, field_name_token.text());
            if member_fn_names.contains(&member_fn_name) {
                return Err(field_name_token.error("structure fields must have distinct names"));
            }
            member_fn_names.push(member_fn_name);
        }

        if !param_names.is_empty()
            && field_types
                .iter()
                .any(|t| t.parametrize(self.module_id, &param_names).has_arbitrary())
        {
            return Err(ss
                .name_token
                .error("generic structures cannot capture outer arbitrary types"));
        }

        // If there's a constraint, add a block to prove it can be satisfied.
        // Validate the complete constraint and its proof before changing parent state.
        let (unbound_constraint, constraint_block) = if let Some(constraint) = &ss.constraint {
            let mut stack = Stack::new();
            for ((name_token, _), t) in ss.fields.iter().zip(&field_types) {
                stack.insert(name_token.to_string(), t.clone());
            }
            let unbound = self.bindings.evaluate_value_with_stack(
                &mut stack,
                project,
                &constraint,
                Some(&AcornType::Bool),
            )?;
            let inhabited = AcornValue::Exists(field_types.clone(), Box::new(unbound.clone()));
            let params = BlockParams::Constraint(inhabited, constraint.range());
            let block = Block::new(
                project,
                &self,
                vec![], // no type params
                vec![], // no args, because we already handled them
                params,
                statement.first_line(),
                statement.last_line(),
                ss.body.as_ref(),
            )?;
            (Some(unbound), Some(block))
        } else {
            (None, None)
        };

        self.add_line_types(
            LineType::Other,
            statement.first_line(),
            ss.first_right_brace.line_number,
        );
        if let Some(block) = constraint_block {
            let proposition = Proposition::inhabited(self.module_id, &ss.name, statement.range());
            let index = self.add_node(project, false, proposition, Some(block));
            self.add_node_lines(index, &statement.range());
        }

        // The member functions take the type itself to a particular member.
        let formals = self.scoped_type_params(&param_names);
        let struct_type = self
            .bindings
            .add_type_family(&ss.name, formals)
            .resolve(arbitrary_params.clone(), &ss.name_token)?;
        self.definition_ranges
            .insert(ss.name.clone(), statement.range());
        let mut member_fns = vec![];
        for (member_fn_name, field_type) in member_fn_names.iter().zip(&field_types) {
            let member_fn_type =
                AcornType::functional(vec![struct_type.clone()], field_type.clone());
            self.bindings.add_constant_named(
                &member_fn_name,
                self.scoped_type_params(&param_names),
                member_fn_type.parametrize(self.module_id, &param_names),
                None,
                None,
            );
            member_fns.push(
                self.bindings
                    .checked_constant_value(&ss.name_token, member_fn_name)?,
            );
        }

        // A "new" function to create one of these struct types.
        let new_fn_name = LocalConstantName::attribute(&ss.name, "new");
        let new_fn_type = AcornType::functional(field_types.clone(), struct_type.clone());
        self.bindings.add_constant_named(
            &new_fn_name,
            self.scoped_type_params(&param_names),
            new_fn_type.parametrize(self.module_id, &param_names),
            None,
            // Invalid inputs can map to the same constrained object. They cannot
            // provide the unique constructor arguments required by match patterns.
            if unbound_constraint.is_none() {
                Some((struct_type.parametrize(self.module_id, &param_names), 0, 1))
            } else {
                None
            },
        );
        // The declaration fixes every actual here, including phantom parameters
        // that a constructor's ordinary field arguments cannot infer.
        let new_fn = AcornValue::constant(
            self.module_id,
            new_fn_name.to_string(),
            arbitrary_params,
            new_fn_type,
        );

        // Each object of this new type has certain properties.
        let object_var = AcornValue::Variable(0, struct_type.clone());
        let mut member_args = vec![];
        for ((name, _), member) in ss.fields.iter().zip(&member_fns) {
            member_args.push(self.bindings.apply_potential(
                name,
                member.clone(),
                vec![object_var.clone()],
                None,
            )?);
        }
        let range = Range {
            start: statement.first_token.start_pos(),
            end: ss.name_token.end_pos(),
        };

        // If there is a constraint, it applies to all instances of the type.
        // constraint(Pair.first(p), Pair.second(p))
        // This is the "constraint equation".
        if let Some(unbound_constraint) = &unbound_constraint {
            let bound_constraint =
                unbound_constraint
                    .clone()
                    .insert_stack(0, 1)
                    .bind_values(1, 1, &member_args);
            let constraint_claim =
                AcornValue::ForAll(vec![struct_type.clone()], Box::new(bound_constraint));
            self.add_node(
                project,
                true,
                Proposition::type_member_definition(
                    constraint_claim.parametrize(self.module_id, &param_names),
                    self.module_id,
                    range,
                    ss.name.clone(),
                    "constraint".into(),
                ),
                None,
            );
        }

        // An object can be recreated by new'ing from its members. Ie:
        // Pair.new(Pair.first(p), Pair.second(p)) = p.
        // This is the "new equation" for a struct type.
        let recreated = self.bindings.apply_potential(
            &ss.name_token,
            crate::binding_map::PotentialValue::Resolved(new_fn.clone()),
            member_args,
            None,
        )?;
        let new_eq =
            AcornValue::Binary(BinaryOp::Equals, Box::new(recreated), Box::new(object_var));
        let new_claim = AcornValue::ForAll(vec![struct_type], Box::new(new_eq))
            .parametrize(self.module_id, &param_names);

        self.add_node(
            project,
            true,
            Proposition::type_member_definition(
                new_claim,
                self.module_id,
                range,
                ss.name.clone(),
                "new".into(),
            ),
            None,
        );

        // There are also formulas for new followed by member functions. Ie:
        //   Pair.first(Pair.new(a, b)) = a.
        // These are the "member equations".
        //
        // When there's a constraint, we need to add it as a condition here, like:
        //   constraint(a, b) -> Pair.first(Pair.new(a, b)) = a.
        let var_args = (0..ss.fields.len())
            .map(|i| AcornValue::Variable(i as AtomId, field_types[i].clone()))
            .collect::<Vec<_>>();
        let new_application = self.bindings.apply_potential(
            &ss.name_token,
            crate::binding_map::PotentialValue::Resolved(new_fn),
            var_args,
            None,
        )?;
        for i in 0..ss.fields.len() {
            let (field_name_token, field_type_expr) = &ss.fields[i];
            let member_fn = &member_fns[i];
            let member_eq = AcornValue::Binary(
                BinaryOp::Equals,
                Box::new(self.bindings.apply_potential(
                    field_name_token,
                    member_fn.clone(),
                    vec![new_application.clone()],
                    None,
                )?),
                Box::new(AcornValue::Variable(i as AtomId, field_types[i].clone())),
            );
            let unbound_member_claim = if let Some(constraint) = &unbound_constraint {
                AcornValue::implies(constraint.clone(), member_eq)
            } else {
                member_eq
            };
            let member_claim =
                AcornValue::ForAll(field_types.clone(), Box::new(unbound_member_claim));
            let range = Range {
                start: field_name_token.start_pos(),
                end: field_type_expr.last_token().end_pos(),
            };
            self.add_node(
                project,
                true,
                Proposition::type_member_definition(
                    member_claim.parametrize(self.module_id, &param_names),
                    self.module_id,
                    range,
                    ss.name.clone(),
                    field_name_token.text().to_string(),
                ),
                None,
            );
        }

        for name in &param_names {
            self.bindings.remove_data_type(name);
        }
        Ok(())
    }

    fn add_inductive_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        is: &crate::statement::InductiveStatement,
    ) -> compilation::Result<()> {
        self.bindings
            .check_typename_available(statement, &is.name)?;
        self.add_other_lines(statement);
        let range = Range {
            start: statement.first_token.start_pos(),
            end: is.name_token.end_pos(),
        };

        // Add the new type first, because we can have self-reference in the inductive type.
        let inductive_type = self.bindings.add_data_type(&is.name);

        // Parse (member name, list of arg types) for each constructor.
        let mut constructors = vec![];
        let mut has_base = false;
        for (name_token, type_list_expr) in &is.constructors {
            let type_list = match type_list_expr {
                Some(expr) => {
                    let mut type_list = vec![];
                    self.bindings
                        .evaluate_type_list(project, expr, &mut type_list)?;
                    type_list
                }
                None => vec![],
            };
            if type_list
                .iter()
                .any(|field| field != &inductive_type && field.refers_to(self.module_id, &is.name))
            {
                self.bindings.remove_data_type(&is.name);
                return Err(name_token
                    .error("recursive constructor fields must use the inductive type directly"));
            }
            if !type_list.contains(&inductive_type) {
                // This provides a base case
                has_base = true;
            }
            let member_name = LocalConstantName::attribute(&is.name, name_token.text());
            constructors.push((member_name, type_list));
        }
        if !has_base {
            return Err(statement.error("inductive type must have a base case"));
        }

        // Define the constructors.
        let mut constructor_fns = vec![];
        let total = constructors.len();
        for (i, (constructor_name, type_list)) in constructors.iter().enumerate() {
            let constructor_type = AcornType::functional(type_list.clone(), inductive_type.clone());
            self.bindings.add_constant_named(
                constructor_name,
                vec![],
                constructor_type,
                None,
                Some((inductive_type.clone(), i, total)),
            );
            constructor_fns.push(
                self.bindings
                    .checked_constant_value(&is.name_token, constructor_name)?
                    .resolved()
                    .expect("generated datatype constants have no type parameters"),
            );
        }

        // The "no confusion" property. Different constructors give different results.
        for i in 0..constructors.len() {
            let (member_name, i_arg_types) = &constructors[i];
            let i_fn = constructor_fns[i].clone();
            let i_vars: Vec<_> = i_arg_types
                .iter()
                .enumerate()
                .map(|(k, t)| AcornValue::Variable(k as AtomId, t.clone()))
                .collect();
            let i_app = AcornValue::apply(i_fn, i_vars);
            for j in 0..i {
                let (_, j_arg_types) = &constructors[j];
                let j_fn = constructor_fns[j].clone();
                let j_vars: Vec<_> = j_arg_types
                    .iter()
                    .enumerate()
                    .map(|(k, t)| {
                        AcornValue::Variable((k + i_arg_types.len()) as AtomId, t.clone())
                    })
                    .collect();
                let j_app = AcornValue::apply(j_fn, j_vars);
                let inequality = AcornValue::not_equals(i_app.clone(), j_app);
                let mut quantifiers = i_arg_types.clone();
                quantifiers.extend(j_arg_types.clone());
                let claim = AcornValue::forall(quantifiers, inequality);
                self.add_node(
                    project,
                    true,
                    Proposition::type_member_definition(
                        claim,
                        self.module_id,
                        range,
                        is.name.clone(),
                        member_name.as_attribute().unwrap().1.to_string(),
                    ),
                    None,
                );
            }
        }

        // The "canonical form" principle. Any item of this type must be created by one
        // of the constructors.
        // It seems like this is implied by induction but let's just stick it in.
        // x0 is going to be the "generic item of this type".
        let mut disjuncts = vec![];
        for (i, constructor_fn) in constructor_fns.iter().enumerate() {
            let (_, arg_types) = &constructors[i];
            let args = arg_types
                .iter()
                .enumerate()
                .map(|(k, t)| AcornValue::Variable((k + 1) as AtomId, t.clone()))
                .collect();
            let app = AcornValue::apply(constructor_fn.clone(), args);
            let var = AcornValue::Variable(0, inductive_type.clone());
            let equality = AcornValue::equals(var, app);
            let exists = AcornValue::exists(arg_types.clone(), equality);
            disjuncts.push(exists);
        }
        let disjunction = AcornValue::reduce(BinaryOp::Or, disjuncts);
        let claim = AcornValue::forall(vec![inductive_type.clone()], disjunction);
        self.add_node(
            project,
            true,
            Proposition::type_member_definition(
                claim,
                self.module_id,
                range,
                is.name.clone(),
                "new".into(),
            ),
            None,
        );

        // The next principle is that each constructor is injective.
        // Ie if Type.construct(x0, x1) = Type.construct(x2, x3) then x0 = x2 and x1 = x3.
        for (i, constructor_fn) in constructor_fns.iter().enumerate() {
            let (member_name, arg_types) = &constructors[i];
            if arg_types.is_empty() {
                continue;
            }

            // First construct the equality.
            // "Type.construct(x0, x1) = Type.construct(x2, x3)"
            let left_args = arg_types
                .iter()
                .enumerate()
                .map(|(k, t)| AcornValue::Variable(k as AtomId, t.clone()))
                .collect();
            let lhs = AcornValue::apply(constructor_fn.clone(), left_args);
            let right_args = arg_types
                .iter()
                .enumerate()
                .map(|(k, t)| AcornValue::Variable((k + arg_types.len()) as AtomId, t.clone()))
                .collect();
            let rhs = AcornValue::apply(constructor_fn.clone(), right_args);
            let equality = AcornValue::equals(lhs, rhs);

            // Then construct the implication, that the corresponding args are equal.
            let mut conjuncts = vec![];
            for (i, arg_type) in arg_types.iter().enumerate() {
                let left = AcornValue::Variable(i as AtomId, arg_type.clone());
                let right = AcornValue::Variable((i + arg_types.len()) as AtomId, arg_type.clone());
                let arg_equality = AcornValue::equals(left, right);
                conjuncts.push(arg_equality);
            }
            let conjunction = AcornValue::reduce(BinaryOp::And, conjuncts);
            let mut forall_types = arg_types.clone();
            forall_types.extend_from_slice(&arg_types);
            let claim =
                AcornValue::forall(forall_types, AcornValue::implies(equality, conjunction));
            self.add_node(
                project,
                true,
                Proposition::type_member_definition(
                    claim,
                    self.module_id,
                    range,
                    is.name.clone(),
                    member_name.as_attribute().unwrap().1.to_string(),
                ),
                None,
            );
        }

        // Structural induction.
        // The type for the inductive hypothesis.
        let hyp_type = AcornType::functional(vec![inductive_type.clone()], AcornType::Bool);
        // x0 represents the inductive hypothesis.
        // Think of the inductive principle as (conjunction) -> (conclusion).
        // The conjunction is a case for each constructor.
        // The conclusion is that x0 holds for all items of the type.
        let mut conjuncts = vec![];
        for (i, constructor_fn) in constructor_fns.iter().enumerate() {
            let (_, arg_types) = &constructors[i];
            let mut args = vec![];
            let mut conditions = vec![];
            for (j, arg_type) in arg_types.iter().enumerate() {
                // x0 is the inductive hypothesis so we start at 1 for the
                // constructor arguments.
                let id = (j + 1) as AtomId;
                args.push(AcornValue::Variable(id, arg_type.clone()));
                if arg_type == &inductive_type {
                    // The inductive case for this constructor includes a condition
                    // that the inductive hypothesis holds for this argument.
                    conditions.push(AcornValue::apply(
                        AcornValue::Variable(0, hyp_type.clone()),
                        vec![AcornValue::Variable(id, arg_type.clone())],
                    ));
                }
            }

            let new_instance = AcornValue::apply(constructor_fn.clone(), args);
            let instance_claim = AcornValue::apply(
                AcornValue::Variable(0, hyp_type.clone()),
                vec![new_instance],
            );
            let unbound = if conditions.is_empty() {
                // This is a base case. We just need to show that the inductive hypothesis
                // holds for this constructor.
                instance_claim
            } else {
                // This is an inductive case. Given the conditions, we show that
                // the inductive hypothesis holds for this constructor.
                AcornValue::implies(
                    AcornValue::reduce(BinaryOp::And, conditions),
                    instance_claim,
                )
            };
            let conjunction_part = AcornValue::forall(arg_types.clone(), unbound);
            conjuncts.push(conjunction_part);
        }
        let conjunction = AcornValue::reduce(BinaryOp::And, conjuncts);
        let conclusion = AcornValue::forall(
            vec![inductive_type.clone()],
            AcornValue::apply(
                AcornValue::Variable(0, hyp_type.clone()),
                vec![AcornValue::Variable(1, inductive_type.clone())],
            ),
        );
        let unbound_claim = AcornValue::implies(conjunction, conclusion);

        // The lambda form is the functional form, which we bind in the environment.
        let name = format!("{}.induction", is.name);
        let lambda_claim = AcornValue::lambda(vec![hyp_type.clone()], unbound_claim.clone());
        self.bindings.add_constant_named(
            &LocalConstantName::attribute(&is.name, "induction"),
            vec![],
            lambda_claim.get_type(),
            Some(lambda_claim),
            None,
        );
        self.bindings.mark_as_theorem(&name);

        // The forall form is the anonymous truth of induction. We add that as a proposition.
        let forall_claim = AcornValue::forall(vec![hyp_type], unbound_claim);
        self.add_node(
            project,
            true,
            Proposition::theorem(true, forall_claim, self.module_id, range, Some(name)),
            None,
        );
        self.definition_ranges
            .insert(is.name.clone(), statement.range());

        Ok(())
    }

    fn typeclass_scope(&self, ts: &TypeclassStatement) -> compilation::Result<BindingMap> {
        for name in [&ts.instance_name, &ts.typeclass_name] {
            self.bindings.check_typename_available(name, name.text())?;
        }
        if ts.instance_name.text() == ts.typeclass_name.text() {
            return Err(ts
                .typeclass_name
                .error("instance and typeclass names must be distinct"));
        }
        let mut scope = self.bindings.clone();
        let class = Typeclass {
            module_id: self.module_id,
            name: ts.typeclass_name.text().to_string(),
        };
        scope.add_typeclass(ts.typeclass_name.text(), class.clone());
        scope.add_arbitrary_type_param(TypeParam {
            name: ts.instance_name.text().to_string(),
            typeclass: Some(class),
        });
        Ok(scope)
    }

    fn prepare_typeclass(
        &self,
        project: &Project,
        ts: &TypeclassStatement,
    ) -> compilation::Result<(BindingMap, Vec<(LocalConstantName, AcornType)>)> {
        let scope = self.typeclass_scope(ts)?;
        let mut names = HashSet::new();
        let mut members = vec![];
        let params = vec![ts.instance_name.text().to_string()];
        for (name, expression) in &ts.constants {
            let constant_name = LocalConstantName::attribute(ts.typeclass_name.text(), name.text());
            if !names.insert(constant_name.clone()) {
                return Err(name.error("typeclass member already defined in this scope"));
            }
            scope.check_constant_name_available(name, &constant_name)?;
            let member_type = scope
                .evaluate_type(project, expression)?
                .parametrize(self.module_id, &params);
            if member_type.has_arbitrary() {
                return Err(
                    expression.error("typeclass member cannot capture an outer arbitrary type")
                );
            }
            members.push((constant_name, member_type));
        }
        Ok((scope, members))
    }

    fn scoped_type_params(&self, names: &[String]) -> Vec<TypeParam> {
        names
            .iter()
            .map(|name| match self.bindings.get_type_for_name(name) {
                Some(AcornType::Variable(param) | AcornType::Arbitrary(param)) => param.clone(),
                _ => panic!("missing scoped type parameter {}", name),
            })
            .collect()
    }

    // Validate ownership before any class or instance member is introduced.
    fn check_canonical_classname(
        &self,
        name_token: &Token,
        potential: &PotentialType,
    ) -> compilation::Result<()> {
        let canonical = match potential {
            PotentialType::Resolved(AcornType::Data(module, name, _)) => (*module, name),
            PotentialType::Unresolved(t) => (t.module_id, &t.name),
            _ => return Err(name_token.error("we can only bind members to data types")),
        };
        if canonical.0 != self.module_id {
            return Err(name_token.error("we can only bind members to types in the current module"));
        }
        if canonical.1 != name_token.text() {
            return Err(name_token.error("we cannot bind members to type aliases"));
        }
        Ok(())
    }

    fn add_class_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        cs: &ClassStatement,
    ) -> compilation::Result<()> {
        self.add_other_lines(statement);
        let potential = self
            .bindings
            .get_type_for_typename(&cs.name)
            .cloned()
            .ok_or_else(|| {
                cs.name_token
                    .error(&format!("undefined type name '{}'", cs.name))
            })?;
        self.check_canonical_classname(&cs.name_token, &potential)?;
        let declared = match &potential {
            PotentialType::Unresolved(family) => family.params.as_slice(),
            _ => &[],
        };
        if cs.type_params.len() != declared.len() {
            return Err(cs.name_token.error(&format!(
                "type {} expects {} parameters, but got {}",
                cs.name,
                declared.len(),
                cs.type_params.len()
            )));
        }
        let params = self
            .bindings
            .evaluate_type_params(project, &cs.type_params)?;
        let mut param_names = Vec::with_capacity(params.len());
        let mut actuals = Vec::with_capacity(params.len());
        for ((param, expression), formal) in params.iter().zip(&cs.type_params).zip(declared) {
            if let Some(bound) = &expression.typeclass {
                if param.typeclass != formal.typeclass {
                    return Err(
                        bound.error("class parameter bound conflicts with the type declaration")
                    );
                }
            }
            actuals.push(self.bindings.add_arbitrary_type_param(TypeParam {
                name: param.name.clone(),
                typeclass: formal.typeclass.clone(),
            }));
            param_names.push(param.name.clone());
        }
        let class_type = potential.resolve(actuals, &cs.name_token)?;
        for substatement in &cs.body.statements {
            match &substatement.statement {
                StatementInfo::Let(ls) => {
                    self.add_let_statement(
                        project,
                        LocalConstantName::attribute(&cs.name, &ls.name),
                        &param_names,
                        ls,
                        substatement.range(),
                    )?;
                }
                StatementInfo::Define(ds) => {
                    self.add_define_statement(
                        project,
                        LocalConstantName::attribute(&cs.name, &ds.name),
                        Some(&class_type),
                        &param_names,
                        ds,
                        substatement.range(),
                    )?;
                }
                _ => {
                    return Err(substatement
                        .error("only let and define statements are allowed in class bodies"))
                }
            }
        }
        for name in param_names {
            self.bindings.remove_data_type(&name);
        }
        Ok(())
    }

    fn add_typeclass_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        ts: &TypeclassStatement,
    ) -> compilation::Result<()> {
        if !self.top_level {
            return Err(statement
                .first_token
                .error("typeclass declarations are only supported at the top level"));
        }
        let (scope, members) = self.prepare_typeclass(project, ts)?;
        let mut staged = self.child(statement.first_line(), true);
        staged.bindings = scope;
        let param = match staged.bindings.get_type_for_name(ts.instance_name.text()) {
            Some(AcornType::Arbitrary(param)) => param.clone(),
            _ => unreachable!("the staged instance type must exist"),
        };
        let params = vec![param.clone()];
        let param_names = vec![param.name.clone()];
        let mut info = TypeclassInfo {
            instance_param: param,
            attributes: ts
                .constants
                .iter()
                .zip(&members)
                .map(|((name, _), (_, member_type))| (name.text().to_string(), member_type.clone()))
                .collect(),
            conditions: Default::default(),
        };
        for (name, member_type) in members {
            staged
                .bindings
                .add_constant_named(&name, params.clone(), member_type, None, None);
        }
        for condition in &ts.conditions {
            let name = condition.name.text();
            let constant_name = LocalConstantName::attribute(ts.typeclass_name.text(), name);
            if info.attributes.contains_key(name) || info.conditions.contains_key(name) {
                return Err(condition
                    .name
                    .error("typeclass member already defined in this scope"));
            }
            staged
                .bindings
                .check_constant_name_available(&condition.name, &constant_name)?;
            let full_name = constant_name.to_string();
            let range = Range {
                start: condition.name.start_pos(),
                end: condition.claim.last_token().end_pos(),
            };
            let (_, _, arg_types, value, _) = staged.bindings.evaluate_scoped_value_named(
                project,
                &[],
                &condition.args,
                None,
                &condition.claim,
                None,
                None,
            )?;
            let unbound_claim = value.ok_or_else(|| {
                condition
                    .claim
                    .error("typeclass conditions must have values")
            })?;
            let claim = AcornValue::forall(arg_types.clone(), unbound_claim.clone())
                .parametrize(self.module_id, &param_names);
            let definition = AcornValue::lambda(arg_types, unbound_claim)
                .parametrize(self.module_id, &param_names);
            if claim.has_arbitrary() || definition.has_arbitrary() {
                return Err(condition
                    .claim
                    .error("typeclass condition cannot capture an outer arbitrary type"));
            }
            claim
                .validate()
                .map_err(|error| condition.claim.error(&error))?;
            definition
                .validate()
                .map_err(|error| condition.claim.error(&error))?;
            staged.bindings.add_constant_named(
                &constant_name,
                params.clone(),
                definition.get_type(),
                Some(definition.clone()),
                None,
            );
            let node = Node::new(
                project,
                &staged,
                true,
                Proposition::theorem(true, claim, self.module_id, range, Some(full_name.clone())),
                None,
            );
            // Inspect the actual exported proposition after theorem-name expansion,
            // exactly as for ordinary bounded theorems. Fact does not retain erased
            // declaration formals, so a closed condition cannot safely be published.
            if !node.claim.value.has_type_variable(&param_names[0]) {
                return Err(condition
                    .name
                    .error("bounded typeclass condition must occur in the exported proposition"));
            }
            staged.bindings.mark_as_theorem(&full_name);
            info.conditions.insert(
                name.to_string(),
                TypeclassCondition {
                    claim: node.claim.value.clone(),
                    definition,
                    range,
                },
            );
            staged.definition_ranges.insert(full_name, range);
            staged.nodes.push(node);
        }
        staged.bindings.add_typeclass_info(
            Typeclass {
                module_id: self.module_id,
                name: ts.typeclass_name.text().to_string(),
            },
            info,
        );
        staged.bindings.remove_data_type(ts.instance_name.text());
        self.bindings = staged.bindings;
        self.definition_ranges = staged.definition_ranges;
        self.nodes.extend(staged.nodes);
        self.add_other_lines(statement);
        Ok(())
    }

    fn add_variable_satisfy_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        vss: &VariableSatisfyStatement,
    ) -> compilation::Result<()> {
        // We need to prove the general existence claim
        let mut stack = Stack::new();
        let (quant_names, quant_types) =
            self.bindings
                .bind_args(&mut stack, project, &vss.declarations, None)?;
        let general_claim_value = self.bindings.evaluate_value_with_stack(
            &mut stack,
            project,
            &vss.condition,
            Some(&AcornType::Bool),
        )?;
        let general_claim = AcornValue::Exists(quant_types.clone(), Box::new(general_claim_value));
        let index = self.add_node(
            project,
            false,
            Proposition::anonymous(general_claim, self.module_id, statement.range()),
            None,
        );
        self.add_node_lines(index, &statement.range());

        // Define the quantifiers as constants
        for (quant_name, quant_type) in quant_names.iter().zip(quant_types.iter()) {
            self.bindings.add_constant_named(
                &LocalConstantName::unqualified(quant_name),
                vec![],
                quant_type.clone(),
                None,
                None,
            );
            self.definition_ranges
                .insert(quant_name.clone(), statement.range());
        }

        // We can then assume the specific existence claim with the named constants
        let specific_claim =
            self.bindings
                .evaluate_value(project, &vss.condition, Some(&AcornType::Bool))?;
        self.add_node(
            project,
            true,
            Proposition::anonymous(specific_claim, self.module_id, statement.range()),
            None,
        );

        Ok(())
    }

    // Privately lower already-validated generic law templates to the checked
    // concrete implementations. Public bound resolution cannot be used here:
    // this is the obligation that must justify the membership in the first place.
    fn lower_instance_conditions(
        &self,
        source: &dyn ErrorSource,
        class: &Typeclass,
        target: &AcornType,
        scope_name: &str,
        info: &TypeclassInfo,
    ) -> compilation::Result<Vec<AcornValue>> {
        if info.instance_param.typeclass.as_ref() != Some(class) {
            return Err(source.error("invalid typeclass condition metadata"));
        }
        let substitution = [(info.instance_param.name.clone(), target.clone())];
        let mut implementations = HashMap::new();
        for (member, template_type) in &info.attributes {
            let value = self
                .bindings
                .get_constant_value(&format!("{}.{}", scope_name, member))
                .and_then(PotentialValue::resolved)
                .ok_or_else(|| source.error("invalid instance implementation metadata"))?;
            if value.get_type() != template_type.instantiate(&substitution) {
                return Err(
                    source.error("instance implementation does not match its class signature")
                );
            }
            value.validate().map_err(|error| source.error(&error))?;
            implementations.insert(format!("{}.{}", class.name, member), value);
        }
        let mut conditions = Vec::with_capacity(info.conditions.len());
        for condition in info.conditions.values() {
            let specialized = condition.claim.instantiate(&substitution);
            let mut references = vec![];
            specialized.find_constants(
                &|constant| {
                    constant.module_id == class.module_id
                        && implementations.contains_key(&constant.name)
                        && constant.params.len() == 1
                        && constant.params[0] == *target
                },
                &mut references,
            );
            for reference in references {
                let implementation = &implementations[&reference.name];
                if reference.instance_type != implementation.get_type() {
                    return Err(source.error("invalid class member in instance condition"));
                }
            }
            let lowered = specialized.replace_constants(0, &|constant, depth| {
                if constant.module_id == class.module_id
                    && constant.params.len() == 1
                    && constant.params[0] == *target
                {
                    implementations
                        .get(&constant.name)
                        .map(|value| value.clone().insert_stack(0, depth))
                } else {
                    None
                }
            });
            if lowered.get_type() != AcornType::Bool
                || lowered.is_generic()
                || lowered.has_arbitrary()
            {
                return Err(source.error("instance condition must be a concrete Boolean claim"));
            }
            lowered.validate().map_err(|error| source.error(&error))?;
            conditions.push(lowered);
        }
        Ok(conditions)
    }

    fn add_instance_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        instance: &crate::statement::InstanceStatement,
    ) -> compilation::Result<()> {
        if !self.top_level {
            return Err(statement
                .first_token
                .error("instance declarations are only supported at the top level"));
        }
        let name = instance.type_name.text();
        let potential = self
            .bindings
            .get_type_for_typename(name)
            .cloned()
            .ok_or_else(|| {
                instance
                    .type_name
                    .error(&format!("undefined type name '{}'", name))
            })?;
        self.check_canonical_classname(&instance.type_name, &potential)?;
        let target = match potential {
            PotentialType::Resolved(AcornType::Data(module, canonical, actuals))
                if actuals.is_empty() =>
            {
                AcornType::Data(module, canonical, actuals)
            }
            _ => {
                return Err(instance.type_name.error(
                    "instance target must be a canonical nongeneric data type in this module",
                ))
            }
        };
        let class = self
            .bindings
            .evaluate_typeclass(project, &instance.typeclass)?;
        if self.bindings.instance_scope(name, &class).is_some() {
            return Err(instance.typeclass.error("instance already defined"));
        }
        let scope_name = format!("{}.{}", name, class.name);
        if self.bindings.instance_scope_in_use(&scope_name) {
            return Err(instance
                .typeclass
                .error("instance namespace conflicts with a different typeclass"));
        }
        let class_bindings = if class.module_id == self.module_id {
            &self.bindings
        } else {
            project.get_bindings(class.module_id).ok_or_else(|| {
                instance
                    .typeclass
                    .error("could not load bindings for typeclass module")
            })?
        };
        let info = class_bindings
            .get_typeclass_info(&class)
            .cloned()
            .ok_or_else(|| {
                instance
                    .typeclass
                    .error("invalid typeclass member metadata")
            })?;
        let mut required = class_bindings
            .instance_member_types(&class, &target)
            .ok_or_else(|| {
                instance
                    .typeclass
                    .error("invalid typeclass member metadata")
            })?;
        let mut checked_members = BTreeMap::new();
        for member in &instance.body.statements {
            let (member_name, member_token) = match &member.statement {
                StatementInfo::Let(ls) => (&ls.name, &ls.name_token),
                StatementInfo::Define(ds) => (&ds.name, &ds.name_token),
                _ => {
                    return Err(member
                        .error("only let and define statements are allowed in instance bodies"))
                }
            };
            required
                .remove(member_name)
                .ok_or_else(|| member_token.error("unknown or duplicate instance member"))?;
            match &member.statement {
                StatementInfo::Let(ls) => {
                    self.add_let_statement(
                        project,
                        LocalConstantName::instance(&class, &ls.name, name),
                        &[],
                        ls,
                        member.range(),
                    )?;
                }
                StatementInfo::Define(ds) => {
                    if !ds.type_params.is_empty() {
                        return Err(ds.type_params[0]
                            .error("instance members cannot declare type parameters"));
                    }
                    self.add_define_statement(
                        project,
                        LocalConstantName::instance(&class, &ds.name, name),
                        Some(&target),
                        &[],
                        ds,
                        member.range(),
                    )?;
                }
                _ => unreachable!(),
            }
            let owner = if class.module_id == self.module_id {
                &self.bindings
            } else {
                project.get_bindings(class.module_id).ok_or_else(|| {
                    instance
                        .typeclass
                        .error("could not load bindings for typeclass module")
                })?
            };
            let pair = self.bindings.check_instance_attribute(
                member_token,
                owner,
                &class,
                &target,
                &scope_name,
                member_name,
            )?;
            checked_members.insert(member_name.clone(), pair);
        }
        if let Some(missing) = required.keys().next() {
            return Err(instance.typeclass.error(&format!(
                "instance is missing required member '{}'",
                missing
            )));
        }
        let conditions = self.lower_instance_conditions(
            &instance.typeclass,
            &class,
            &target,
            &scope_name,
            &info,
        )?;
        if !conditions.is_empty() || instance.proof.is_some() {
            let goal = if conditions.is_empty() {
                // An optional law-free proof body is still checked in full.
                AcornValue::Bool(true)
            } else {
                AcornValue::reduce(BinaryOp::And, conditions)
            };
            let mut proof_env = self.child(statement.first_line(), instance.proof.is_none());
            // Permit the concrete implementation namespace in the proof body,
            // while denying every generic use of this provisional membership.
            // Block::new must capture this denied scope before any body children.
            proof_env
                .bindings
                .add_instance_scope(name, class.clone(), scope_name.clone());
            proof_env
                .bindings
                .deny_instance(self.module_id, name, &class);
            let range = Range {
                start: statement.first_token.start_pos(),
                end: instance.body.right_brace.end_pos(),
            };
            let block = Block::new(
                project,
                &proof_env,
                vec![],
                vec![],
                BlockParams::Instance(goal, range),
                statement.first_line(),
                statement.last_line(),
                instance.proof.as_ref(),
            )?;
            // Export only a vacuous marker from the obligation. Its lowered law
            // is not a premise inside the block, nor an unconditional new axiom.
            let proposition = Proposition::instance(
                None,
                self.module_id,
                statement.range(),
                name.to_string(),
                class.name.clone(),
            );
            let index = self.add_node(project, false, proposition, Some(block));
            self.add_node_lines(index, &statement.range());
        }
        // Later goals may use this declaration conditionally on the whole module
        // verifying; a failed obligation prevents completed module publication.
        self.bindings
            .add_instance_scope(name, class.clone(), scope_name.clone());
        // These definitions are available only after the obligation boundary.
        // The proof block was already captured under its own denied membership;
        // neither these facts nor this widened outer scope can enter that block.
        for (member, (generic, implementation)) in checked_members {
            let claim = AcornValue::equals(generic, implementation);
            claim
                .validate()
                .map_err(|error| instance.typeclass.error(&error))?;
            self.add_node(
                project,
                true,
                Proposition::type_member_definition(
                    claim,
                    self.module_id,
                    statement.range(),
                    name.to_string(),
                    format!("instance.{}.{}", class.name, member),
                ),
                None,
            );
        }
        self.add_other_lines(statement);
        Ok(())
    }

    // Adds a statement to the environment.
    // If the statement has a body, this call creates a sub-environment and adds the body
    // to that sub-environment.
    pub fn add_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
    ) -> compilation::Result<()> {
        if !matches!(
            statement.statement,
            StatementInfo::Structure(_) | StatementInfo::Class(_) | StatementInfo::Instance(_)
        ) {
            return self.add_statement_inner(project, statement);
        }
        // Declaration admission is transactional; failures cannot leak temporary parameters,
        // generated members, proof facts, or source visibility into the parent environment.
        let bindings = self.bindings.clone();
        let definitions = self.definition_ranges.clone();
        let line_count = self.line_types.len();
        let node_count = self.nodes.len();
        let explicit_false = self.includes_explicit_false;
        let result = self.add_statement_inner(project, statement);
        if result.is_err() {
            self.bindings = bindings;
            self.definition_ranges = definitions;
            self.line_types.truncate(line_count);
            self.nodes.truncate(node_count);
            self.includes_explicit_false = explicit_false;
        }
        result
    }

    fn add_statement_inner(
        &mut self,
        project: &mut Project,
        statement: &Statement,
    ) -> compilation::Result<()> {
        if self.includes_explicit_false {
            return Err(
                statement.error("an explicit 'false' may not be followed by other statements")
            );
        }
        match &statement.statement {
            StatementInfo::Type(ts) => {
                self.add_other_lines(statement);
                self.bindings
                    .check_typename_available(statement, &ts.name)?;
                if ts.type_expr.is_axiom() {
                    self.bindings.add_data_type(&ts.name);
                } else {
                    let potential = self
                        .bindings
                        .evaluate_potential_type(project, &ts.type_expr)?;
                    self.bindings.add_potential_type_alias(&ts.name, potential);
                };
                self.definition_ranges
                    .insert(ts.name.clone(), statement.range());
                Ok(())
            }

            StatementInfo::Let(ls) => {
                self.add_other_lines(statement);
                self.add_let_statement(
                    project,
                    LocalConstantName::unqualified(&ls.name),
                    &[],
                    ls,
                    statement.range(),
                )
            }

            StatementInfo::Define(ds) => {
                self.add_other_lines(statement);
                self.add_define_statement(
                    project,
                    LocalConstantName::unqualified(&ds.name),
                    None,
                    &[],
                    ds,
                    statement.range(),
                )
            }

            StatementInfo::Theorem(ts) => self.add_theorem_statement(project, statement, ts),

            StatementInfo::Prop(ps) => {
                let claim =
                    self.bindings
                        .evaluate_value(project, &ps.claim, Some(&AcornType::Bool))?;
                if claim == AcornValue::Bool(false) {
                    self.includes_explicit_false = true;
                }

                if self.bindings.is_citation(project, &claim) {
                    // We already know this is true, so we don't need to prove it
                    self.add_node(
                        project,
                        true,
                        Proposition::anonymous(claim, self.module_id, statement.range()),
                        None,
                    );
                    self.add_other_lines(statement);
                } else {
                    let index = self.add_node(
                        project,
                        false,
                        Proposition::anonymous(claim, self.module_id, statement.range()),
                        None,
                    );
                    self.add_node_lines(index, &statement.range());
                }
                Ok(())
            }

            StatementInfo::ForAll(fas) => {
                if fas.body.statements.is_empty() {
                    // ForAll statements with an empty body can just be ignored
                    return Ok(());
                }
                let mut args = vec![];
                for quantifier in &fas.quantifiers {
                    let (arg_name, arg_type) =
                        self.bindings.evaluate_declaration(project, quantifier)?;
                    args.push((arg_name, arg_type));
                }

                let block = Block::new(
                    project,
                    &self,
                    vec![],
                    args,
                    BlockParams::ForAll,
                    statement.first_line(),
                    statement.last_line(),
                    Some(&fas.body),
                )?;

                let (outer_claim, range) = block.export_last_claim(self, &fas.body.right_brace)?;

                let index = self.add_node(
                    project,
                    false,
                    Proposition::anonymous(outer_claim, self.module_id, range),
                    Some(block),
                );
                self.add_node_lines(index, &statement.range());
                Ok(())
            }

            StatementInfo::If(is) => {
                let condition =
                    self.bindings
                        .evaluate_value(project, &is.condition, Some(&AcornType::Bool))?;
                let range = is.condition.range();
                let if_claim = self.add_conditional(
                    project,
                    condition.clone(),
                    range,
                    statement.first_line(),
                    statement.last_line(),
                    &is.body,
                    None,
                )?;
                if let Some(else_body) = &is.else_body {
                    self.add_conditional(
                        project,
                        condition.negate(),
                        range,
                        else_body.left_brace.line_number as u32,
                        else_body.right_brace.line_number as u32,
                        else_body,
                        if_claim,
                    )?;
                }
                Ok(())
            }

            StatementInfo::VariableSatisfy(vss) => {
                self.add_variable_satisfy_statement(project, statement, vss)
            }

            StatementInfo::FunctionSatisfy(fss) => {
                self.add_function_satisfy_statement(project, statement, fss)
            }

            StatementInfo::Structure(ss) => self.add_structure_statement(project, statement, ss),

            StatementInfo::Inductive(is) => self.add_inductive_statement(project, statement, is),

            StatementInfo::Import(is) => {
                self.add_other_lines(statement);

                // Give a local name to the imported module
                let local_name = is.components.last().unwrap();
                self.bindings
                    .check_unqualified_name_available(statement, local_name)?;
                let full_name = is.components.join(".");
                let module_id = match project.load_module_by_name(&full_name) {
                    Ok(module_id) => module_id,
                    Err(LoadError(s)) => {
                        // The error is with the import statement itself, like a circular import.
                        return Err(statement.error(&format!("import error: {}", s)));
                    }
                };
                if project.get_bindings(module_id).is_none() {
                    // The fundamental error is in the other module, not this one.
                    return Err(Error::secondary(
                        &statement.first_token,
                        &statement.last_token,
                        &format!("error in '{}' module", full_name),
                    ));
                }
                self.bindings.import_module(local_name, module_id);
                self.bindings
                    .import_instance_members(project.get_bindings(module_id).unwrap());
                self.definition_ranges
                    .insert(local_name.clone(), statement.range());

                // Bring the imported names into this environment
                for name in &is.names {
                    self.bindings.import_name(project, module_id, name)?;
                    self.definition_ranges
                        .insert(name.text().to_string(), statement.range());
                }

                Ok(())
            }

            StatementInfo::Class(cs) => self.add_class_statement(project, statement, cs),

            StatementInfo::Numerals(ds) => {
                self.add_other_lines(statement);
                let acorn_type = self.bindings.evaluate_type(project, &ds.type_expr)?;
                if let AcornType::Data(module, typename, actuals) = acorn_type {
                    if !actuals.is_empty() {
                        return Err(ds
                            .type_expr
                            .error("numerals type cannot have type parameters"));
                    }
                    self.bindings.set_default(module, typename);
                    Ok(())
                } else {
                    Err(ds.type_expr.error("numerals type must be a data type"))
                }
            }

            StatementInfo::Solve(ss) => {
                let target = self.bindings.evaluate_value(project, &ss.target, None)?;
                let solve_range = Range {
                    start: statement.first_token.start_pos(),
                    end: ss.target.last_token().end_pos(),
                };

                let mut block = Block::new(
                    project,
                    &self,
                    vec![],
                    vec![],
                    BlockParams::Solve(target.clone(), solve_range),
                    statement.first_line(),
                    statement.last_line(),
                    Some(&ss.body),
                )?;

                let prop = match block.solves(self, &target) {
                    Some((outer_claim, claim_range)) => {
                        block.goal = None;
                        Proposition::anonymous(outer_claim, self.module_id, claim_range)
                    }
                    None => {
                        // The block doesn't contain a solution.
                        // So, it has no claim that can be exported. It doesn't really make sense
                        // to export whatever the last proposition is.
                        // A lot of code expects something, though, so put a vacuous "true" in here.
                        Proposition::anonymous(
                            AcornValue::Bool(true),
                            self.module_id,
                            statement.range(),
                        )
                    }
                };

                let index = self.add_node(project, false, prop, Some(block));
                self.add_node_lines(index, &statement.range());
                Ok(())
            }

            StatementInfo::Problem(body) => {
                let block = Block::new(
                    project,
                    &self,
                    vec![],
                    vec![],
                    BlockParams::Problem,
                    statement.first_line(),
                    statement.last_line(),
                    Some(body),
                )?;

                // It would be nice to not have to make a vacuous "true" proposition here.
                let vacuous_prop = Proposition::anonymous(
                    AcornValue::Bool(true),
                    self.module_id,
                    statement.range(),
                );

                let index = self.add_node(project, false, vacuous_prop, Some(block));
                self.add_node_lines(index, &statement.range());
                Ok(())
            }

            StatementInfo::Typeclass(ts) => self.add_typeclass_statement(project, statement, ts),

            StatementInfo::Instance(instance) => {
                self.add_instance_statement(project, statement, instance)
            }

            StatementInfo::Match(ms) => {
                let scrutinee = self.bindings.evaluate_value(project, &ms.scrutinee, None)?;
                let scrutinee_type = scrutinee.get_type();
                let mut cases = vec![];
                let mut indices = vec![];
                let mut all_cases = false;
                for (pattern, body) in &ms.cases {
                    let (constructor, args, index, total) =
                        self.bindings
                            .evaluate_pattern(project, &scrutinee_type, pattern)?;
                    if indices.contains(&index) {
                        return Err(pattern.error("duplicate pattern in match statement"));
                    }
                    indices.push(index);
                    if total == indices.len() {
                        all_cases = true;
                    }
                    cases.push((constructor, args, pattern, body));
                }
                if !all_cases {
                    return Err(ms
                        .scrutinee
                        .error("not all cases are covered in match statement"));
                }
                // Build every case before changing the parent. A rejected body must not
                // leave earlier case claims or partial proof obligations behind.
                let mut blocks = vec![];
                let mut disjuncts = vec![];
                for (constructor, args, pattern, body) in cases {
                    let params = BlockParams::MatchCase(
                        scrutinee.clone(),
                        constructor,
                        args,
                        pattern.range(),
                    );
                    let block = Block::new(
                        project,
                        self,
                        vec![],
                        vec![],
                        params,
                        body.left_brace.line_number,
                        body.right_brace.line_number,
                        Some(body),
                    )?;
                    let (claim, _) = block.export_last_claim(self, &body.right_brace)?;
                    disjuncts.push(claim);
                    blocks.push((block, body.range()));
                }

                // All branches are exhaustive and retain their own proof obligations.
                // Only their disjunction is usable after the complete case split.
                let mut exported = Some(AcornValue::reduce(BinaryOp::Or, disjuncts));
                let last = blocks.len() - 1;
                for (index, (block, range)) in blocks.into_iter().enumerate() {
                    let claim = if index == last {
                        exported.take().unwrap()
                    } else {
                        AcornValue::Bool(true)
                    };
                    let prop = Proposition::anonymous(claim, self.module_id, statement.range());
                    let node_index = self.add_node(project, false, prop, Some(block));
                    self.add_node_lines(node_index, &range);
                }
                self.add_line_types(
                    LineType::Other,
                    statement.last_line(),
                    statement.last_line(),
                );
                Ok(())
            }
        }
    }

    // Parse these tokens and add them to the environment.
    // If project is not provided, we won't be able to handle import statements.
    pub fn add_tokens(
        &mut self,
        project: &mut Project,
        tokens: Vec<Token>,
    ) -> compilation::Result<()> {
        let mut tokens = TokenIter::new(tokens);
        loop {
            match Statement::parse(&mut tokens, false) {
                Ok((Some(statement), _)) => {
                    if let Err(e) = self.add_statement(project, &statement) {
                        return Err(e);
                    }
                }
                Ok((None, _)) => return Ok(()),
                Err(e) => return Err(e),
            }
        }
    }

    // Every module imported anywhere in this file contributes to proof identity,
    // including imports local to a nested proof. This inventory does not grant
    // any fact visibility outside the lexical scope of its import.
    pub(crate) fn proof_dependencies(&self) -> Vec<ModuleId> {
        fn collect(env: &Environment, dependencies: &mut BTreeSet<ModuleId>) {
            dependencies.extend(env.bindings.direct_dependencies());
            for node in &env.nodes {
                if let Some(block) = &node.block {
                    collect(&block.env, dependencies);
                }
            }
        }
        let mut dependencies = BTreeSet::new();
        collect(self, &mut dependencies);
        dependencies.into_iter().collect()
    }

    // Get all facts that this environment exports.
    pub fn exported_facts(&self) -> Vec<Fact> {
        self.exported_facts_filtered(None)
    }

    // All principles with a selected source remain available, including several
    // facts generated from one datatype member. Anonymous facts use their line ID.
    pub fn exported_facts_filtered(&self, filter: Option<&HashSet<String>>) -> Vec<Fact> {
        assert!(self.top_level);
        let mut facts = vec![];
        for node in &self.nodes {
            if filter.is_some_and(|names| {
                !node
                    .claim
                    .source
                    .fact_name()
                    .is_some_and(|name| names.contains(&name))
            }) {
                continue;
            }
            facts.push(Fact::new(node.claim.clone(), Truthiness::Factual));
        }
        facts
    }

    // Returns a NodeCursor for all nodes that correspond to a goal within this environment,
    // or subenvironments, recursively.
    // The order is "proving order", ie the goals inside the block are listed before the
    // root goal of a block.
    pub fn iter_goals(&self) -> impl Iterator<Item = NodeCursor> {
        let mut answer = vec![];
        for i in 0..self.nodes.len() {
            let mut cursor = NodeCursor::new(self, i);
            cursor.find_goals(&mut answer);
        }
        answer.into_iter()
    }

    // Compatibility alias: this lookup has always used the displayed description.
    pub fn get_node_by_name(&self, name: &str) -> NodeCursor {
        self.get_node_by_description(name)
    }

    // Testing helper, not a stable source-identity lookup.
    pub fn get_node_by_description(&self, description: &str) -> NodeCursor {
        let mut descriptions = Vec::new();
        for node in self.iter_goals() {
            let context = node.goal_context().unwrap();
            if context.description() == description {
                return node;
            }
            descriptions.push(context.name);
        }

        panic!(
            "no context found for {} in:\n{}\n",
            description,
            descriptions.join("\n")
        );
    }

    // Returns the path to a given zero-based line.
    // This is a UI heuristic.
    // Either returns a path to a proposition, or an error message explaining why this
    // line is unusable.
    // Error messages use one-based line numbers.
    pub fn path_for_line(&self, line: u32) -> Result<Vec<usize>, String> {
        let mut path = vec![];
        let mut block: Option<&Block> = None;
        let mut env = self;
        loop {
            match env.get_line_type(line) {
                Some(LineType::Node(i)) => {
                    path.push(i);
                    let prop = &env.nodes[i];
                    if prop.claim.source.is_axiom() {
                        return Err(format!("line {} is an axiom", line + 1));
                    }
                    match &prop.block {
                        Some(b) => {
                            block = Some(b);
                            env = &b.env;
                            continue;
                        }
                        None => {
                            return Ok(path);
                        }
                    }
                }
                Some(LineType::Opening) | Some(LineType::Closing) => match block {
                    Some(block) => {
                        if block.goal.is_none() {
                            return Err(format!("no claim for block at line {}", line + 1));
                        }
                        return Ok(path);
                    }
                    None => return Err(format!("brace but no block, line {}", line + 1)),
                },
                Some(LineType::Other) => return Err(format!("line {} is not a prop", line + 1)),
                None => return Err(format!("line {} is out of range", line + 1)),
                Some(LineType::Empty) => {
                    // We let the user insert a proof in an area by clicking on an empty
                    // line where the proof would go.
                    // To find the statement we're proving, we "slide" into the next prop.
                    let mut slide = line;
                    loop {
                        slide += 1;
                        match env.get_line_type(slide) {
                            Some(LineType::Node(i)) => {
                                let prop = &env.nodes[i];
                                if prop.claim.source.is_axiom() {
                                    return Err(format!("slide to axiom, line {}", slide + 1));
                                }
                                if prop.block.is_none() {
                                    path.push(i);
                                    return Ok(path);
                                }
                                // We can't slide into a block, because the proof would be
                                // inserted into the block, rather than here.
                                return Err(format!("blocked slide {} -> {}", line + 1, slide + 1));
                            }
                            Some(LineType::Empty) => {
                                // Keep sliding
                                continue;
                            }
                            Some(LineType::Closing) => {
                                // Sliding into the end of our block is okay
                                match block {
                                    Some(block) => {
                                        if block.goal.is_none() {
                                            return Err("slide to end but no claim".to_string());
                                        }
                                        return Ok(path);
                                    }
                                    None => {
                                        return Err(format!(
                                            "close brace but no block, line {}",
                                            slide + 1
                                        ))
                                    }
                                }
                            }
                            Some(LineType::Opening) => {
                                return Err(format!("slide to open brace, line {}", slide + 1));
                            }
                            Some(LineType::Other) => {
                                return Err(format!("slide to non-prop {}", slide + 1));
                            }
                            None => return Err(format!("slide to end, line {}", slide + 1)),
                        }
                    }
                }
            }
        }
    }

    pub fn covers_line(&self, line: u32) -> bool {
        if line < self.first_line {
            return false;
        }
        if line >= self.next_line() {
            return false;
        }
        true
    }
}

// Methods used for integration testing.
impl Environment {
    // Create a test version of the environment.
    pub fn test() -> Self {
        use crate::module::FIRST_NORMAL;
        Environment::new(FIRST_NORMAL)
    }

    // Compatibility entry point for callers using the original constructor name.
    pub fn new_test() -> Self {
        Self::test()
    }

    // Adds a possibly multi-line statement to the environment.
    // Panics on failure.
    pub fn add(&mut self, input: &str) {
        let tokens = Token::scan(input);
        if let Err(e) = self.add_tokens(&mut Project::new_mock(), tokens) {
            panic!("error in add_tokens: {}", e);
        }
    }

    // Makes sure the lines are self-consistent
    pub fn check_lines(&self) {
        // Check that each proposition's block covers the lines it claims to cover
        for (line, line_type) in self.line_types.iter().enumerate() {
            if let LineType::Node(prop_index) = line_type {
                let prop = &self.nodes[*prop_index];
                if let Some(block) = &prop.block {
                    assert!(block.env.covers_line(line as u32));
                }
            }
        }

        // Recurse
        for prop in &self.nodes {
            if let Some(block) = &prop.block {
                block.env.check_lines();
            }
        }
    }

    // Expects the given line to be bad
    pub fn bad(&mut self, input: &str) {
        if let Ok(statement) = Statement::parse_str(input) {
            assert!(
                self.add_statement(&mut Project::new_mock(), &statement)
                    .is_err(),
                "expected error in: {}",
                input
            );
        }
    }

    // Check that the given name actually does have this type in the environment.
    pub fn expect_type(&mut self, name: &str, type_string: &str) {
        self.bindings.expect_type(name, type_string)
    }

    // Check that the given name is defined to be this value
    pub fn expect_def(&mut self, name: &str, value_string: &str) {
        let env_value = match self.bindings.get_definition(name) {
            Some(t) => t,
            None => panic!("{} not found in environment", name),
        };
        assert_eq!(env_value.to_string(), value_string);
    }

    // Assert that these two names are defined to equal the same thing
    pub fn assert_def_eq(&self, name1: &str, name2: &str) {
        let def1 = self.bindings.get_definition(name1).unwrap();
        let def2 = self.bindings.get_definition(name2).unwrap();
        assert_eq!(def1, def2);
    }

    // Assert that these two names are defined to be different things
    pub fn assert_def_ne(&self, name1: &str, name2: &str) {
        let def1 = self.bindings.get_definition(name1).unwrap();
        let def2 = self.bindings.get_definition(name2).unwrap();
        assert_ne!(def1, def2);
    }
}
