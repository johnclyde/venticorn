// Modified for Venticorn: staged match binding and constructor metadata.
use std::collections::{BTreeMap, HashMap, HashSet};

use tower_lsp::lsp_types::{CompletionItem, CompletionItemKind, Range};

use crate::acorn_type::{AcornType, PotentialType, TypeParam, Typeclass, UnresolvedType};
use crate::acorn_value::{AcornValue, BinaryOp, ConstantInstance};
use crate::atom::AtomId;
use crate::code_gen_error::CodeGenError;
use crate::compilation::{self, Error, ErrorSource};
use crate::constant_name::LocalConstantName;
use crate::expression::{Declaration, Expression, Terminator, TypeParamExpr};
use crate::module::{ModuleId, FIRST_NORMAL};
use crate::project::Project;
use crate::proof_scope::ProofScope;
use crate::termination_checker::TerminationChecker;
use crate::token::{self, Token, TokenIter, TokenType};

// A representation of the variables on the stack.
pub struct Stack {
    // Maps the name of the variable to their depth and their type.
    vars: HashMap<String, (AtomId, AcornType)>,
}

impl Stack {
    pub fn new() -> Self {
        Stack {
            vars: HashMap::new(),
        }
    }

    pub fn names(&self) -> Vec<&str> {
        let mut answer: Vec<&str> = vec![""; self.vars.len()];
        for (name, (i, _)) in &self.vars {
            answer[*i as usize] = name;
        }
        answer
    }

    pub fn insert(&mut self, name: String, acorn_type: AcornType) -> AtomId {
        let i = self.vars.len() as AtomId;
        self.vars.insert(name, (i, acorn_type));
        i
    }

    fn remove(&mut self, name: &str) {
        self.vars.remove(name);
    }

    pub fn remove_all(&mut self, names: &[String]) {
        for name in names {
            self.remove(name);
        }
    }

    // Returns the depth and type of the variable with this name.
    fn get(&self, name: &str) -> Option<&(AtomId, AcornType)> {
        self.vars.get(name)
    }
}

// In order to convert an Expression to an AcornValue, we need to convert the string representation
// of types, variable names, and constant names into numeric identifiers, detect name collisions,
// and typecheck everything.
// The BindingMap handles this. It does not handle Statements, just Expressions.
// It does not have to be efficient enough to run in the inner loop of the prover.
#[derive(Clone)]
pub struct BindingMap {
    // The module all these names are in.
    module: ModuleId,
    // Tiny declaration positions avoid storing a complete binding map on every node.
    position: usize,
    name_positions: HashMap<String, usize>,
    instance_member_positions: HashMap<(ModuleId, String), usize>,
    default_history: Vec<(usize, ModuleId, String)>,
    hidden_codegen_names: HashSet<String>,

    // Maps the name of a type to the type object.
    typename_to_type: BTreeMap<String, PotentialType>,

    // Maps the type object to the name of a type.
    type_to_typename: HashMap<AcornType, String>,

    // Family aliases are distinct from aliases for one complete specialized type.
    generic_type_aliases: HashMap<(ModuleId, String, usize), String>,

    // Class names have their own kind, while sharing the declaration namespace.
    name_to_typeclass: BTreeMap<String, Typeclass>,
    // Definitions owned by this module; imported aliases do not create new owners.
    typeclass_definitions: HashMap<Typeclass, TypeclassInfo>,
    typeclass_to_name: HashMap<Typeclass, String>,

    // Successfully admitted concrete implementations, keyed by canonical local data
    // name and canonical class. This records declarations, not bound membership.
    instance_scopes: HashMap<(String, Typeclass), String>,
    proof_scope: ProofScope,

    // Formatting metadata only; evaluation always consults the canonical owner.
    imported_instance_members: HashMap<(ModuleId, String), Typeclass>,

    // Maps an identifier name to its type.
    // Has entries for both defined constants and aliases. Pending generic aliases
    // retain the signature in declaration parameters, before actuals are supplied.
    constant_name_to_type: BTreeMap<String, AcornType>,

    // Maps the name of a constant defined in this scope to information about it.
    // Doesn't handle variables defined on the stack, only ones that will be in scope for the
    // entirety of this environment.
    // Aliases are stored separately and resolve to their canonical constant.
    // Includes "<datatype>.<constant>" for members.
    constant_info: BTreeMap<String, ConstantInfo>,

    // The canonical identifier of a constant is the first place it is defined.
    // There may be other names in this environment that refer to the same thing.
    // When we create an AcornValue, we want to use the canonical name.
    // Preserve unresolved declarations as well as fully specialized values.
    aliases: HashMap<String, PotentialValue>,

    // Whenever a name from some other scope has a local alias in this one,
    // if we're generating code, we prefer to use the local name.
    // Thus, preferred_names maps the canonical identifier to a local alias.
    canonical_to_alias: HashMap<(ModuleId, String), String>,

    // Names that refer to other modules.
    // For example after "import foo", "foo" refers to a module.
    name_to_module: BTreeMap<String, ModuleId>,

    // The local name for imported modules.
    module_to_name: HashMap<ModuleId, String>,

    // The default data type to use for numeric literals.
    default: Option<(ModuleId, String)>,

    // Whether this constant is the name of a theorem in this context.
    // Inside the block containing the proof of a theorem, the name is not considered to
    // be a theorem.
    theorems: HashSet<String>,
}

// A condition retains a generic, expanded proposition for instance obligations,
// plus its generic lambda for a separately published callable theorem name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeclassCondition {
    pub claim: AcornValue,
    pub definition: AcornValue,
    pub range: Range,
}

// A class definition separates required member signatures from logical conditions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeclassInfo {
    pub instance_param: TypeParam,
    pub attributes: BTreeMap<String, AcornType>,
    pub conditions: BTreeMap<String, TypeclassCondition>,
}

// A generic declaration whose type arguments have not been inferred yet.
#[derive(Clone, Debug, PartialEq)]
pub struct UnresolvedConstant {
    module_id: ModuleId,
    name: String,
    // Formal parameters are kept in declaration order.
    params: Vec<TypeParam>,
    generic_type: AcornType,
}

impl UnresolvedConstant {
    fn resolve(
        &self,
        source: &dyn ErrorSource,
        actuals: Vec<AcornType>,
        scope: &ProofScope,
    ) -> compilation::Result<AcornValue> {
        if actuals.len() != self.params.len() {
            return Err(source.error(&format!(
                "expected {} type parameters, but got {}",
                self.params.len(),
                actuals.len()
            )));
        }
        for (formal, actual) in self.params.iter().zip(&actuals) {
            if !formal.accepts_in_scope(actual, scope) {
                return Err(source.error(&format!(
                    "type argument {} does not satisfy the class bound on {}",
                    actual, formal.name
                )));
            }
        }
        let substitutions = self
            .params
            .iter()
            .zip(&actuals)
            .map(|(formal, actual)| (formal.name.clone(), actual.clone()))
            .collect::<Vec<_>>();
        let instance_type = self.generic_type.instantiate(&substitutions);
        Ok(AcornValue::new_constant(
            self.module_id,
            self.name.clone(),
            actuals,
            instance_type,
        ))
    }
}

// A named declaration may still need type arguments before it becomes a proof value.
#[derive(Clone, Debug, PartialEq)]
pub enum PotentialValue {
    Unresolved(UnresolvedConstant),
    Resolved(AcornValue),
}

impl PotentialValue {
    // Internal callers use this only after introducing a constant with no type parameters.
    pub fn resolved(self) -> Option<AcornValue> {
        match self {
            PotentialValue::Resolved(value) => Some(value),
            PotentialValue::Unresolved(..) => None,
        }
    }

    // Pending declarations expose their generic signature only to inference.
    pub fn get_type(&self) -> AcornType {
        match self {
            PotentialValue::Unresolved(unresolved) => unresolved.generic_type.clone(),
            PotentialValue::Resolved(value) => value.get_type(),
        }
    }

    fn to_named_entity(self) -> NamedEntity {
        match self {
            PotentialValue::Unresolved(unresolved) => NamedEntity::Unresolved(unresolved),
            PotentialValue::Resolved(value) => NamedEntity::Value(value),
        }
    }

    pub fn value(self, source: &dyn ErrorSource) -> compilation::Result<AcornValue> {
        match self {
            PotentialValue::Resolved(value) => Ok(value),
            PotentialValue::Unresolved(unresolved) => Err(source.error(&format!(
                "value {} requires type arguments",
                unresolved.name
            ))),
        }
    }
}

#[derive(Clone)]
struct ConstantInfo {
    // The names of the type parameters this constant was defined with, if any.
    // These type parameters can be used in the definition.
    params: Vec<TypeParam>,

    // The definition of this constant, if it has one.
    definition: Option<AcornValue>,

    // If this constant is a constructor, store:
    //   the type it constructs
    //   an index of which constructor it is
    //   how many total constructors there are
    constructor: Option<(AcornType, usize, usize)>,
}

// Return an error if the types don't match.
// This doesn't do full polymorphic typechecking, but it will fail if there's no
// way that the types can match, for example if a function expects T -> Nat and
// the value provided is Nat.
// actual_type should be non-generic here.
// expected_type can be generic.
pub fn check_type<'a>(
    source: &dyn ErrorSource,
    expected_type: Option<&AcornType>,
    actual_type: &AcornType,
) -> compilation::Result<()> {
    if let Some(e) = expected_type {
        if e != actual_type {
            return Err(source.error(&format!("expected type {}, but this is {}", e, actual_type)));
        }
    }
    Ok(())
}

fn keys_with_prefix<'a, T>(
    map: &'a BTreeMap<String, T>,
    prefix: &'a str,
) -> impl Iterator<Item = &'a String> {
    map.range(prefix.to_string()..)
        .take_while(move |(key, _)| key.starts_with(prefix))
        .map(|(key, _)| key)
}

// A name can refer to any of these things.
enum NamedEntity {
    Value(AcornValue),
    Type(AcornType),
    Module(ModuleId),
    Typeclass(Typeclass),
    Instance(ModuleId, String),
    Unresolved(UnresolvedConstant),
    UnresolvedType(UnresolvedType),
}

impl NamedEntity {
    fn expect_potential_value(
        self,
        expected_type: Option<&AcornType>,
        source: &dyn ErrorSource,
    ) -> compilation::Result<PotentialValue> {
        match self {
            NamedEntity::Unresolved(unresolved) => Ok(PotentialValue::Unresolved(unresolved)),
            entity => Ok(PotentialValue::Resolved(
                entity.expect_value(expected_type, source)?,
            )),
        }
    }

    fn expect_value(
        self,
        expected_type: Option<&AcornType>,
        source: &dyn ErrorSource,
    ) -> compilation::Result<AcornValue> {
        match self {
            NamedEntity::Unresolved(unresolved) => Err(source.error(&format!(
                "value {} requires type arguments",
                unresolved.name
            ))),
            NamedEntity::Value(value) => {
                check_type(source, expected_type, &value.get_type())?;
                Ok(value)
            }
            NamedEntity::Type(_) | NamedEntity::UnresolvedType(_) => {
                Err(source.error("name refers to a type but we expected a value"))
            }
            NamedEntity::Module(_) => {
                Err(source.error("name refers to a module but we expected a value"))
            }
            NamedEntity::Typeclass(_) => {
                Err(source.error("name refers to a typeclass but we expected a value"))
            }
            NamedEntity::Instance(..) => Err(source.error("instance namespace is not a value")),
        }
    }

    fn expect_type(self, source: &dyn ErrorSource) -> compilation::Result<AcornType> {
        match self {
            NamedEntity::Unresolved(unresolved) => Err(source.error(&format!(
                "value {} requires type arguments",
                unresolved.name
            ))),
            NamedEntity::Value(_) => {
                Err(source.error("name refers to a value but we expected a type"))
            }
            NamedEntity::Type(t) => Ok(t),
            NamedEntity::UnresolvedType(t) => Err(source.error(&format!(
                "type {} requires {} type parameters",
                t.name,
                t.params.len()
            ))),
            NamedEntity::Module(_) => {
                Err(source.error("name refers to a module but we expected a type"))
            }
            NamedEntity::Typeclass(_) => {
                Err(source.error("name refers to a typeclass but we expected a type"))
            }
            NamedEntity::Instance(..) => Err(source.error("instance namespace is not a type")),
        }
    }
}

impl BindingMap {
    pub fn new(module: ModuleId) -> Self {
        assert!(module >= FIRST_NORMAL);
        let mut answer = BindingMap {
            module,
            position: 0,
            name_positions: HashMap::new(),
            instance_member_positions: HashMap::new(),
            default_history: vec![],
            hidden_codegen_names: HashSet::new(),
            typename_to_type: BTreeMap::new(),
            type_to_typename: HashMap::new(),
            generic_type_aliases: HashMap::new(),
            name_to_typeclass: BTreeMap::new(),
            typeclass_definitions: HashMap::new(),
            typeclass_to_name: HashMap::new(),
            instance_scopes: HashMap::new(),
            proof_scope: ProofScope::default(),
            imported_instance_members: HashMap::new(),
            constant_name_to_type: BTreeMap::new(),
            constant_info: BTreeMap::new(),
            aliases: HashMap::new(),
            canonical_to_alias: HashMap::new(),
            name_to_module: BTreeMap::new(),
            module_to_name: HashMap::new(),
            default: None,
            theorems: HashSet::new(),
        };
        answer.add_type_alias("Bool", AcornType::Bool);
        answer
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Simple helper functions.
    ////////////////////////////////////////////////////////////////////////////////

    fn record_name(&mut self, name: &str) {
        self.position += 1;
        self.name_positions.insert(name.to_owned(), self.position);
    }

    pub(crate) fn codegen_position(&self) -> usize {
        self.position
    }

    // Build only when code is actually requested, retaining the selected lexical names.
    pub(crate) fn for_codegen_at(&self, position: usize, scope: &ProofScope) -> Self {
        let mut result = self.clone();
        result.proof_scope = scope.clone();
        result.hidden_codegen_names.extend(
            self.name_positions
                .iter()
                .filter(|(_, p)| **p > position)
                .map(|(name, _)| name.clone()),
        );
        result.name_positions.retain(|_, p| *p <= position);
        let visible = &result.name_positions;
        result
            .typename_to_type
            .retain(|name, _| visible.contains_key(name));
        result
            .name_to_typeclass
            .retain(|name, _| visible.contains_key(name));
        result
            .constant_name_to_type
            .retain(|name, _| visible.contains_key(name));
        result
            .constant_info
            .retain(|name, _| visible.contains_key(name));
        result.aliases.retain(|name, _| visible.contains_key(name));
        result
            .name_to_module
            .retain(|name, _| visible.contains_key(name));
        result.imported_instance_members.retain(|key, _| {
            self.instance_member_positions
                .get(key)
                .is_some_and(|p| *p <= position)
        });
        result.theorems.retain(|name| visible.contains_key(name));
        result.type_to_typename.clear();
        result.generic_type_aliases.clear();
        result.typeclass_to_name.clear();
        result.canonical_to_alias.clear();
        result.module_to_name.clear();
        let mut names = result
            .name_positions
            .iter()
            .map(|(n, p)| (*p, n.clone()))
            .collect::<Vec<_>>();
        names.sort();
        for (_, name) in names {
            if let Some(ty) = result.typename_to_type.get(&name) {
                match ty {
                    PotentialType::Resolved(ty) => {
                        result
                            .type_to_typename
                            .entry(ty.clone())
                            .or_insert_with(|| name.clone());
                        if let AcornType::Data(module, family, actuals) = ty {
                            if actuals.is_empty() {
                                result
                                    .canonical_to_alias
                                    .entry((*module, family.clone()))
                                    .or_insert_with(|| name.clone());
                            }
                        }
                    }
                    PotentialType::Unresolved(ty) => {
                        result
                            .generic_type_aliases
                            .entry((ty.module_id, ty.name.clone(), ty.params.len()))
                            .or_insert_with(|| name.clone());
                        result
                            .canonical_to_alias
                            .entry((ty.module_id, ty.name.clone()))
                            .or_insert_with(|| name.clone());
                    }
                }
            }
            if let Some(class) = result.name_to_typeclass.get(&name) {
                result
                    .typeclass_to_name
                    .entry(class.clone())
                    .or_insert_with(|| name.clone());
            }
            if let Some(alias) = result.aliases.get(&name) {
                let canonical = match alias {
                    PotentialValue::Unresolved(c) => Some((c.module_id, c.name.clone())),
                    PotentialValue::Resolved(v) => v
                        .as_simple_constant()
                        .map(|(id, name)| (id, name.to_owned())),
                };
                if let Some((module, canonical)) = canonical {
                    if module != result.module {
                        result
                            .canonical_to_alias
                            .entry((module, canonical))
                            .or_insert_with(|| name.clone());
                    }
                }
            }
            // Module spelling intentionally prefers the last visible import alias.
            if let Some(module) = result.name_to_module.get(&name) {
                result.module_to_name.insert(*module, name);
            }
        }
        result.default = self
            .default_history
            .iter()
            .rev()
            .find(|(p, _, _)| *p <= position)
            .map(|(_, m, n)| (*m, n.clone()));
        result
    }

    pub fn name_in_use(&self, name: &str) -> bool {
        self.typename_to_type.contains_key(name)
            || self.name_to_typeclass.contains_key(name)
            || self.constant_name_to_type.contains_key(name)
            || self.name_to_module.contains_key(name)
    }

    // Availability checks deliberately cover every namespace. Dotted spelling
    // collisions must be rejected even when structured canonical identities differ.
    pub fn lowercase_name_in_use(&self, name: &str) -> bool {
        self.constant_name_in_use(&LocalConstantName::Unqualified(name.to_string()))
    }

    pub fn constant_name_in_use(&self, name: &LocalConstantName) -> bool {
        self.name_in_use(&name.to_string())
    }

    pub fn typename_in_use(&self, name: &str) -> bool {
        self.name_in_use(name)
    }

    fn insert_type_name(&mut self, name: String, acorn_type: AcornType) {
        assert!(!self.name_in_use(&name), "type name {} already bound", name);
        self.record_name(&name);
        self.type_to_typename
            .entry(acorn_type.clone())
            .or_insert_with(|| name.clone());
        self.typename_to_type
            .insert(name, PotentialType::Resolved(acorn_type));
    }

    // A generic declaration is not a usable type until all ordered actuals are supplied.
    pub fn add_potential_type(&mut self, name: &str, num_params: usize) -> PotentialType {
        self.add_type_family(
            name,
            (0..num_params)
                .map(|i| TypeParam::unconstrained(&format!("T{}", i)))
                .collect(),
        )
    }

    // Retain complete ordered bounds separately from preferred family spelling.
    pub fn add_type_family(&mut self, name: &str, params: Vec<TypeParam>) -> PotentialType {
        if params.is_empty() {
            return PotentialType::Resolved(self.add_data_type(name));
        }
        assert!(!self.name_in_use(name), "type name {} already bound", name);
        let potential = PotentialType::Unresolved(UnresolvedType {
            module_id: self.module,
            name: name.into(),
            params,
        });
        self.record_name(name);
        self.typename_to_type.insert(name.into(), potential.clone());
        potential
    }

    pub fn get_type_for_typename(&self, name: &str) -> Option<&PotentialType> {
        self.typename_to_type.get(name)
    }

    pub fn get_potential_type_for_name(&self, name: &str) -> Option<&PotentialType> {
        self.get_type_for_typename(name)
    }

    // Adds a new data type to the binding map.
    // Panics if the name is already bound.
    pub fn add_data_type(&mut self, name: &str) -> AcornType {
        if self.name_in_use(name) {
            panic!("type name {} already bound", name);
        }
        let data_type = AcornType::Data(self.module, name.to_string(), vec![]);
        self.insert_type_name(name.to_string(), data_type.clone());
        data_type
    }

    // Introduce a fixed but otherwise unknown type within a proof scope.
    pub fn add_arbitrary_type(&mut self, name: &str) -> AcornType {
        self.add_arbitrary_type_param(TypeParam::unconstrained(name))
    }

    // Preserve the defining class identity while introducing a scoped instance parameter.
    pub fn add_arbitrary_type_with_class(
        &mut self,
        name: &str,
        typeclass: Option<&Typeclass>,
    ) -> AcornType {
        self.add_arbitrary_type_param(TypeParam {
            name: name.to_string(),
            typeclass: typeclass.cloned(),
        })
    }

    // Introduce a complete descriptor without reconstructing its canonical class bound.
    // Panics if the name is already bound, like the compatibility constructors above.
    pub fn add_arbitrary_type_param(&mut self, param: TypeParam) -> AcornType {
        assert!(
            !self.name_in_use(&param.name),
            "type name {} already bound",
            param.name
        );
        let name = param.name.clone();
        let arbitrary = AcornType::Arbitrary(param);
        self.insert_type_name(name, arbitrary.clone());
        arbitrary
    }

    // Adds a new type name that's an alias for an existing type
    pub fn add_type_alias(&mut self, name: &str, acorn_type: AcornType) {
        if self.name_in_use(name) {
            panic!("type alias {} already bound", name);
        }
        if let AcornType::Data(module, type_name, actuals) = &acorn_type {
            // A specialized type alias must not rename the entire generic family.
            if actuals.is_empty() {
                self.canonical_to_alias
                    .entry((*module, type_name.clone()))
                    .or_insert(name.to_string());
            }
        }
        self.insert_type_name(name.to_string(), acorn_type);
    }

    // Add a name for a complete type or an unspecialized generic family.
    pub fn add_potential_type_alias(&mut self, name: &str, potential: PotentialType) {
        match potential {
            PotentialType::Resolved(t) => self.add_type_alias(name, t),
            PotentialType::Unresolved(t) => {
                assert!(!self.name_in_use(name), "type alias {} already bound", name);
                self.record_name(name);
                self.generic_type_aliases
                    .entry((t.module_id, t.name.clone(), t.params.len()))
                    .or_insert_with(|| name.to_string());
                self.canonical_to_alias
                    .entry((t.module_id, t.name.clone()))
                    .or_insert_with(|| name.to_string());
                self.typename_to_type
                    .insert(name.to_string(), PotentialType::Unresolved(t));
            }
        }
    }

    fn add_type_variable(&mut self, name: &str, typeclass: Option<Typeclass>) {
        assert!(
            !self.name_in_use(name),
            "type variable {} already bound",
            name
        );
        self.insert_type_name(
            name.to_string(),
            AcornType::Variable(crate::acorn_type::TypeParam {
                name: name.to_string(),
                typeclass: typeclass,
            }),
        );
    }

    pub fn add_typeclass(&mut self, name: &str, typeclass: Typeclass) {
        assert!(!self.name_in_use(name), "name {} already bound", name);
        self.record_name(name);
        self.typeclass_to_name
            .entry(typeclass.clone())
            .or_insert_with(|| name.to_string());
        self.name_to_typeclass.insert(name.to_string(), typeclass);
    }

    pub(crate) fn add_typeclass_info(&mut self, class: Typeclass, info: TypeclassInfo) {
        assert_eq!(class.module_id, self.module);
        assert_eq!(info.instance_param.typeclass.as_ref(), Some(&class));
        assert!(self.typeclass_definitions.insert(class, info).is_none());
    }

    pub fn get_typeclass_info(&self, class: &Typeclass) -> Option<&TypeclassInfo> {
        self.typeclass_definitions.get(class)
    }

    pub fn get_typeclass_for_name(&self, name: &str) -> Option<&Typeclass> {
        self.name_to_typeclass.get(name)
    }

    pub fn get_name_for_typeclass(&self, typeclass: &Typeclass) -> Option<&str> {
        self.typeclass_to_name.get(typeclass).map(String::as_str)
    }

    // Specialize the defining module's explicit class metadata for preparation.
    // This does not grant public class-member application or bound membership.
    pub(crate) fn instance_member_types(
        &self,
        class: &Typeclass,
        target: &AcornType,
    ) -> Option<BTreeMap<String, AcornType>> {
        let info = self.get_typeclass_info(class)?;
        if class.module_id != self.module
            || self.get_typeclass_for_name(&class.name) != Some(class)
            || info.instance_param.typeclass.as_ref() != Some(class)
        {
            return None;
        }
        let substitution = [(info.instance_param.name.clone(), target.clone())];
        Some(
            info.attributes
                .iter()
                .map(|(name, member_type)| (name.clone(), member_type.instantiate(&substitution)))
                .collect(),
        )
    }

    // Check both sides of an instance member relationship against the complete
    // canonical class descriptor. This does not publish membership or a fact.
    pub(crate) fn check_instance_attribute(
        &self,
        source: &dyn ErrorSource,
        owner: &BindingMap,
        class: &Typeclass,
        target: &AcornType,
        scope: &str,
        member: &str,
    ) -> compilation::Result<(AcornValue, AcornValue)> {
        let info = owner
            .get_typeclass_info(class)
            .ok_or_else(|| source.error("invalid typeclass member metadata"))?;
        if owner.module != class.module_id
            || owner.get_typeclass_for_name(&class.name) != Some(class)
            || info.instance_param.typeclass.as_ref() != Some(class)
        {
            return Err(source.error("invalid canonical typeclass metadata"));
        }
        let generic_name = format!("{}.{}", class.name, member);
        let template_type = info
            .attributes
            .get(member)
            .ok_or_else(|| source.error("invalid canonical class member metadata"))?;
        if owner.get_params(&generic_name) != [info.instance_param.clone()]
            || owner.get_type_for_constant_name(&generic_name) != Some(template_type)
            || !matches!(
                owner.get_constant_value(&generic_name),
                Some(PotentialValue::Unresolved(_))
            )
        {
            return Err(source.error("invalid canonical class member metadata"));
        }
        let expected =
            template_type.instantiate(&[(info.instance_param.name.clone(), target.clone())]);
        let implementation = self
            .get_constant_value(&format!("{}.{}", scope, member))
            .and_then(PotentialValue::resolved);
        if implementation.as_ref().map(AcornValue::get_type).as_ref() != Some(&expected) {
            return Err(source.error(&format!(
                "instance member '{}' must have type {}",
                member, expected
            )));
        }
        let implementation = implementation.unwrap();
        implementation
            .validate()
            .map_err(|error| source.error(&error))?;
        let generic = AcornValue::new_constant(
            class.module_id,
            generic_name,
            vec![target.clone()],
            expected,
        );
        generic.validate().map_err(|error| source.error(&error))?;
        Ok((generic, implementation))
    }

    pub(crate) fn instance_scope(&self, target: &str, class: &Typeclass) -> Option<&str> {
        self.instance_scopes
            .get(&(target.to_string(), class.clone()))
            .map(String::as_str)
    }

    pub(crate) fn instance_scope_in_use(&self, scope: &str) -> bool {
        self.instance_scopes.values().any(|value| value == scope)
    }

    pub fn proof_scope(&self) -> &ProofScope {
        &self.proof_scope
    }

    pub(crate) fn deny_instance(&mut self, module: ModuleId, name: &str, class: &Typeclass) {
        self.proof_scope.deny_instance(module, name, class);
    }

    pub(crate) fn add_instance_scope(&mut self, target: &str, class: Typeclass, scope: String) {
        self.proof_scope
            .record_instance(self.module, target, &class);
        assert!(!self.instance_scope_in_use(&scope));
        assert!(self
            .instance_scopes
            .insert((target.to_string(), class), scope)
            .is_none());
    }

    // Look up a constant without treating a pending generic declaration as a proof value.
    pub fn get_constant_value(&self, name: &str) -> Option<PotentialValue> {
        if let Some(value) = self.aliases.get(name) {
            return Some(value.clone());
        }

        // Constants defined here
        let constant_type = self.constant_name_to_type.get(name)?.clone();
        let params = self.constant_info.get(name)?.params.clone();
        if params.is_empty() {
            Some(PotentialValue::Resolved(AcornValue::new_constant(
                self.module,
                name.to_string(),
                vec![],
                constant_type,
            )))
        } else {
            Some(PotentialValue::Unresolved(UnresolvedConstant {
                module_id: self.module,
                name: name.to_string(),
                params,
                generic_type: constant_type,
            }))
        }
    }

    // Gets the type for an identifier, not for a type name.
    // E.g. if let x: Nat = 0, then get_type("x") will give you Nat.
    pub fn get_type_for_constant_name(&self, name: &str) -> Option<&AcornType> {
        self.constant_name_to_type.get(name)
    }

    pub fn get_type_for_identifier(&self, identifier: &str) -> Option<&AcornType> {
        self.get_type_for_constant_name(identifier)
    }

    pub fn get_params(&self, identifier: &str) -> Vec<TypeParam> {
        match self.constant_info.get(identifier) {
            Some(info) => info.params.clone(),
            None => vec![],
        }
    }

    // Gets the type for a type name, not for an identifier.
    pub fn get_type_for_name(&self, type_name: &str) -> Option<&AcornType> {
        match self.typename_to_type.get(type_name) {
            Some(PotentialType::Resolved(t)) => Some(t),
            _ => None,
        }
    }

    pub fn has_typename(&self, type_name: &str) -> bool {
        self.typename_to_type.contains_key(type_name)
    }

    pub fn has_type_name(&self, type_name: &str) -> bool {
        self.has_typename(type_name)
    }

    pub fn has_constant_name(&self, name: &str) -> bool {
        self.constant_name_to_type.contains_key(name)
    }

    pub fn has_identifier(&self, identifier: &str) -> bool {
        self.has_constant_name(identifier)
    }

    // Returns the defined value, if there is a defined value.
    // If there isn't, returns None.
    pub fn get_definition(&self, name: &str) -> Option<&AcornValue> {
        self.constant_info.get(name)?.definition.as_ref()
    }

    // Returns the defined value and its parameters in declaration order.
    pub fn get_definition_and_params(&self, name: &str) -> Option<(&AcornValue, &[TypeParam])> {
        let info = self.constant_info.get(name)?;
        Some((info.definition.as_ref()?, &info.params))
    }

    // All other modules that we directly depend on, besides this one.
    // Sorted by the name of the import, so that the order will be consistent.
    pub fn direct_dependencies(&self) -> Vec<ModuleId> {
        self.name_to_module.values().copied().collect()
    }

    pub fn set_default(&mut self, module: ModuleId, type_name: String) {
        self.position += 1;
        self.default_history
            .push((self.position, module, type_name.clone()));
        self.default = Some((module, type_name));
    }

    // Adds a constant.
    // This can also add members, by providing a name like "Foo.bar".
    pub fn add_constant(
        &mut self,
        name: &str,
        params: Vec<TypeParam>,
        constant_type: AcornType,
        definition: Option<AcornValue>,
        constructor: Option<(AcornType, usize, usize)>,
    ) {
        if self.name_in_use(name) {
            panic!("constant name {} already bound", name);
        }
        if let Some(value) = &definition {
            value.validate().unwrap_or_else(|error| {
                panic!("invalid definition for constant {}: {}", name, error)
            });
        }
        if params.is_empty() {
            assert!(
                !constant_type.has_generic(),
                "generic constant type needs declared parameters"
            );
            assert!(
                !definition.as_ref().is_some_and(AcornValue::has_generic),
                "generic definition needs declared parameters"
            );
        } else {
            assert!(
                !constant_type.has_arbitrary(),
                "generic constant type cannot capture arbitrary types"
            );
            assert!(
                !definition.as_ref().is_some_and(AcornValue::has_arbitrary),
                "generic definition cannot capture arbitrary types"
            );
        }
        self.record_name(name);
        self.constant_name_to_type
            .insert(name.to_string(), constant_type);

        let info = ConstantInfo {
            params,
            definition,
            constructor,
        };
        self.constant_info.insert(name.to_string(), info);
    }

    // Adds a local alias for an already-existing constant.
    pub fn add_alias(
        &mut self,
        name: &str,
        canonical_module: ModuleId,
        canonical_name: String,
        value: PotentialValue,
    ) {
        if self.name_in_use(name) {
            panic!("cannot alias name {} because it is already bound", name);
        }
        self.record_name(name);
        self.constant_name_to_type
            .insert(name.to_string(), value.get_type());
        let canonical = (canonical_module, canonical_name);
        if canonical_module != self.module {
            // Prefer this alias locally to using the qualified, canonical name
            self.canonical_to_alias
                .entry(canonical.clone())
                .or_insert(name.to_string());
        }
        self.aliases.insert(name.to_string(), value);
    }

    pub fn is_constant(&self, name: &str) -> bool {
        self.constant_info.contains_key(name)
    }

    pub fn mark_as_theorem(&mut self, name: &str) {
        self.theorems.insert(name.to_string());
    }

    pub fn is_theorem(&self, name: &str) -> bool {
        self.theorems.contains(name)
    }

    // Data types that come from type parameters get removed when they go out of scope.
    pub fn remove_data_type(&mut self, name: &str) {
        self.name_positions.remove(name);
        match self.typename_to_type.remove(name) {
            Some(PotentialType::Resolved(t)) => {
                self.type_to_typename.remove(&t);
            }
            Some(PotentialType::Unresolved(_)) => {}
            None => panic!("removing data type {} which is already not present", name),
        }
    }

    pub fn import_module(&mut self, name: &str, module: ModuleId) {
        if self.name_in_use(name) {
            panic!("module name {} already bound", name);
        }
        self.record_name(name);
        self.name_to_module.insert(name.to_string(), module);
        self.module_to_name.insert(module, name.to_string());
        self.proof_scope.import(module);
    }

    pub(crate) fn import_instance_members(&mut self, owner: &BindingMap) {
        self.proof_scope.include_memberships(&owner.proof_scope);
        for ((_, class), scope) in &owner.instance_scopes {
            if owner.get_constant_value(scope).is_some() {
                continue;
            }
            for name in keys_with_prefix(&owner.constant_info, &format!("{}.", scope)) {
                let key = (owner.module, name.clone());
                if !self.instance_member_positions.contains_key(&key) {
                    self.position += 1;
                    self.instance_member_positions
                        .insert(key.clone(), self.position);
                }
                self.imported_instance_members.insert(key, class.clone());
            }
        }
    }

    pub fn is_module(&self, name: &str) -> bool {
        self.name_to_module.contains_key(name)
    }

    // Whether this value is calling a theorem on some arguments.
    pub fn is_citation(&self, project: &Project, claim: &AcornValue) -> bool {
        match claim.is_named_function_call() {
            Some((module_id, name)) => {
                if module_id == self.module {
                    self.is_theorem(&name)
                } else {
                    let bindings = project.get_bindings(module_id).unwrap();
                    bindings.is_theorem(&name)
                }
            }
            None => false,
        }
    }

    // Members are looked up through the type's canonical defining module.
    fn get_member_completions(
        &self,
        project: &Project,
        data_type: &AcornType,
        prefix: &str,
        instance: Option<&AcornValue>,
        visible: &dyn Fn(&str) -> bool,
    ) -> Option<Vec<CompletionItem>> {
        let (module, type_name) = match data_type {
            AcornType::Data(module, name, _) => (*module, name),
            AcornType::Variable(param) | AcornType::Arbitrary(param) => {
                let class = param.typeclass.as_ref()?;
                (class.module_id, &class.name)
            }
            _ => return None,
        };
        self.get_named_member_completions(project, module, type_name, prefix, instance, visible)
    }

    fn get_named_member_completions(
        &self,
        project: &Project,
        module: ModuleId,
        type_name: &str,
        prefix: &str,
        instance: Option<&AcornValue>,
        visible: &dyn Fn(&str) -> bool,
    ) -> Option<Vec<CompletionItem>> {
        let bindings = if module == self.module {
            self
        } else {
            project.get_bindings(module)?
        };
        let full_prefix = format!("{}.{}", type_name, prefix);
        let mut items = vec![];
        for name in keys_with_prefix(&bindings.constant_name_to_type, &full_prefix) {
            if module == self.module && !visible(name) {
                continue;
            }
            let member = name.strip_prefix(&format!("{}.", type_name))?;
            if member.contains('.') {
                continue;
            }
            if let Some(instance) = instance {
                let token = TokenType::Identifier.new_token(member);
                if self
                    .evaluate_instance_attribute(&token, project, instance.clone(), member)
                    .is_err()
                {
                    continue;
                }
            }
            items.push(CompletionItem {
                label: member.to_string(),
                kind: Some(CompletionItemKind::FIELD),
                ..Default::default()
            });
        }
        Some(items)
    }

    // Complete an identifier or name chain. Import completion exposes only canonical exports.
    pub fn get_completions(
        &self,
        project: &Project,
        prefix: &str,
        importing: bool,
    ) -> Option<Vec<CompletionItem>> {
        self.get_completions_visible(project, prefix, importing, &|_| true)
    }

    pub fn get_completions_visible(
        &self,
        project: &Project,
        prefix: &str,
        importing: bool,
        visible: &dyn Fn(&str) -> bool,
    ) -> Option<Vec<CompletionItem>> {
        if prefix.is_empty() && !importing {
            return None;
        }
        if let Some((namespace, partial)) = prefix.rsplit_once('.') {
            if importing || namespace.split('.').any(str::is_empty) {
                return None;
            }
            let mut entity = None;
            for name in namespace.split('.') {
                let local_name = match &entity {
                    None => Some(name.to_string()),
                    Some(NamedEntity::Type(AcornType::Data(module, type_name, _)))
                        if *module == self.module =>
                    {
                        Some(format!("{}.{}", type_name, name))
                    }
                    Some(NamedEntity::Value(value)) => match value.get_type() {
                        AcornType::Data(module, type_name, _) if module == self.module => {
                            Some(format!("{}.{}", type_name, name))
                        }
                        _ => None,
                    },
                    _ => None,
                };
                if local_name.as_deref().is_some_and(|name| !visible(name)) {
                    return None;
                }
                let kind = if name.chars().all(|ch| ch.is_ascii_digit()) {
                    TokenType::Numeral
                } else {
                    TokenType::Identifier
                };
                let token = kind.new_token(name);
                entity = Some(
                    self.evaluate_name(&token, project, &Stack::new(), entity)
                        .ok()?,
                );
            }
            return match entity? {
                NamedEntity::Instance(module, scope) => self
                    .get_named_member_completions(project, module, &scope, partial, None, visible),
                NamedEntity::Typeclass(class) => self.get_named_member_completions(
                    project,
                    class.module_id,
                    &class.name,
                    partial,
                    None,
                    visible,
                ),
                NamedEntity::Unresolved(_) => Some(vec![]),
                NamedEntity::UnresolvedType(t) => self.get_member_completions(
                    project,
                    &AcornType::Data(t.module_id, t.name, vec![]),
                    partial,
                    None,
                    visible,
                ),
                NamedEntity::Module(module) => project
                    .get_bindings(module)?
                    .get_completions(project, partial, true),
                NamedEntity::Type(data_type) => {
                    self.get_member_completions(project, &data_type, partial, None, visible)
                }
                NamedEntity::Value(value) => self.get_member_completions(
                    project,
                    &value.get_type(),
                    partial,
                    Some(&value),
                    visible,
                ),
            };
        }
        let mut items = vec![];
        if !importing {
            for keyword in token::keywords_with_prefix(prefix) {
                items.push(CompletionItem {
                    label: keyword.to_string(),
                    kind: Some(CompletionItemKind::KEYWORD),
                    ..Default::default()
                });
            }
        }
        for name in keys_with_prefix(&self.constant_name_to_type, prefix) {
            if !visible(name) {
                continue;
            }
            if importing && (self.aliases.contains_key(name) || self.theorems.contains(name)) {
                continue;
            }
            if !name.contains('.') {
                items.push(CompletionItem {
                    label: name.clone(),
                    kind: Some(CompletionItemKind::CONSTANT),
                    ..Default::default()
                });
            }
        }
        for name in keys_with_prefix(&self.typename_to_type, prefix) {
            if !visible(name) {
                continue;
            }
            if importing {
                let canonical = match self.typename_to_type.get(name) {
                    Some(PotentialType::Resolved(AcornType::Data(module, canonical, _))) => {
                        *module == self.module && canonical == name
                    }
                    Some(PotentialType::Unresolved(t)) => {
                        t.module_id == self.module && &t.name == name
                    }
                    _ => false,
                };
                if !canonical {
                    continue;
                }
            }
            items.push(CompletionItem {
                label: name.clone(),
                kind: Some(CompletionItemKind::CLASS),
                ..Default::default()
            });
        }
        if !importing {
            for name in keys_with_prefix(&self.name_to_typeclass, prefix) {
                if visible(name) {
                    items.push(CompletionItem {
                        label: name.clone(),
                        kind: Some(CompletionItemKind::INTERFACE),
                        ..Default::default()
                    });
                }
            }
            for name in keys_with_prefix(&self.name_to_module, prefix) {
                if !visible(name) {
                    continue;
                }
                items.push(CompletionItem {
                    label: name.clone(),
                    kind: Some(CompletionItemKind::MODULE),
                    ..Default::default()
                });
            }
        }
        Some(items)
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Tools for parsing Expressions and similar structures
    ////////////////////////////////////////////////////////////////////////////////

    // Evaluates an expression that represents a type.
    pub fn evaluate_type(
        &self,
        project: &Project,
        expression: &Expression,
    ) -> compilation::Result<AcornType> {
        match self.evaluate_potential_type(project, expression)? {
            PotentialType::Resolved(t) => Ok(t),
            PotentialType::Unresolved(t) => Err(expression.error(&format!(
                "type {} requires {} type parameters",
                t.name,
                t.params.len()
            ))),
        }
    }

    pub fn evaluate_potential_type(
        &self,
        project: &Project,
        expression: &Expression,
    ) -> compilation::Result<PotentialType> {
        match expression {
            Expression::Singleton(token) => {
                if token.token_type == TokenType::Axiom {
                    return Err(token.error("axiomatic types can only be created at the top level"));
                }
                if let Some(acorn_type) = self.typename_to_type.get(token.text()) {
                    Ok(acorn_type.clone())
                } else if self.name_to_typeclass.contains_key(token.text()) {
                    Err(token.error("name refers to a typeclass but we expected a type"))
                } else {
                    Err(token.error("expected type name"))
                }
            }
            Expression::Unary(token, _) => {
                Err(token.error("unexpected unary operator in type expression"))
            }
            Expression::Binary(left, token, right) => match token.token_type {
                TokenType::RightArrow => {
                    let arg_exprs = left.flatten_list(true)?;
                    let mut arg_types = vec![];
                    for arg_expr in arg_exprs {
                        arg_types.push(self.evaluate_type(project, arg_expr)?);
                    }
                    let return_type = self.evaluate_type(project, right)?;
                    Ok(PotentialType::Resolved(AcornType::new_functional(
                        arg_types,
                        return_type,
                    )))
                }
                TokenType::Dot => {
                    let entity = self.evaluate_entity(&mut Stack::new(), project, expression)?;
                    match entity {
                        NamedEntity::UnresolvedType(t) => Ok(PotentialType::Unresolved(t)),
                        other => Ok(PotentialType::Resolved(other.expect_type(token)?)),
                    }
                }
                _ => Err(token.error("unexpected binary operator in type expression")),
            },
            Expression::Apply(left, params) => {
                let Expression::Grouping(opening, inner, _) = params.as_ref() else {
                    return Err(params.error("expected type parameters in type application"));
                };
                if opening.token_type != TokenType::LessThan {
                    return Err(opening.error("expected '<' for type parameters"));
                }
                let actuals = inner
                    .flatten_comma_separated_list()
                    .into_iter()
                    .map(|arg| self.evaluate_type(project, arg))
                    .collect::<compilation::Result<Vec<_>>>()?;
                let potential = self.evaluate_potential_type(project, left)?;
                Ok(PotentialType::Resolved(potential.resolve_in_scope(
                    actuals,
                    expression,
                    &self.proof_scope,
                )?))
            }
            Expression::Grouping(_, e, _) => self.evaluate_potential_type(project, e),
            Expression::Binder(token, _, _, _) | Expression::IfThenElse(token, _, _, _, _) => {
                Err(token.error("unexpected token in type expression"))
            }
            Expression::Match(token, _, _, _) => {
                Err(token.error("unexpected match token in type expression"))
            }
        }
    }

    // Evaluates a list of types.
    pub fn evaluate_type_list(
        &self,
        project: &Project,
        expression: &Expression,
        output: &mut Vec<AcornType>,
    ) -> compilation::Result<()> {
        match expression {
            Expression::Grouping(_, e, _) => self.evaluate_type_list(project, e, output),
            Expression::Binary(left, token, right) if token.token_type == TokenType::Comma => {
                self.evaluate_type_list(project, left, output)?;
                self.evaluate_type_list(project, right, output)
            }
            e => {
                output.push(self.evaluate_type(project, e)?);
                Ok(())
            }
        }
    }

    // Evaluates a variable declaration in this context.
    // expect_self is whether we expect this to be a "self" declaration.
    pub fn evaluate_declaration(
        &self,
        project: &Project,
        declaration: &Declaration,
    ) -> compilation::Result<(String, AcornType)> {
        match declaration {
            Declaration::Typed(name_token, type_expr) => {
                let acorn_type = self.evaluate_type(project, &type_expr)?;
                return Ok((name_token.to_string(), acorn_type));
            }
            Declaration::SelfToken(name_token) => {
                return Err(name_token.error("cannot use 'self' as an argument here"));
            }
        };
    }

    // Parses a list of named argument declarations and adds them to the stack.
    // class_type should be provided if these are the arguments of a new member function.
    pub fn bind_args<'a, I>(
        &self,
        stack: &mut Stack,
        project: &Project,
        declarations: I,
        class_type: Option<&AcornType>,
    ) -> compilation::Result<(Vec<String>, Vec<AcornType>)>
    where
        I: IntoIterator<Item = &'a Declaration>,
    {
        let mut names = Vec::new();
        let mut types = Vec::new();
        for (i, declaration) in declarations.into_iter().enumerate() {
            if class_type.is_some() && i == 0 {
                match declaration {
                    Declaration::SelfToken(_) => {
                        names.push("self".to_string());
                        types.push(class_type.unwrap().clone());
                        continue;
                    }
                    _ => {
                        return Err(declaration
                            .token()
                            .error("first argument of a member function must be 'self'"));
                    }
                }
            }
            let (name, acorn_type) = self.evaluate_declaration(project, declaration)?;
            if self.name_in_use(&name) {
                return Err(declaration
                    .token()
                    .error("cannot redeclare a name in an argument list"));
            }
            if names.contains(&name) {
                return Err(declaration
                    .token()
                    .error("cannot declare a name twice in one argument list"));
            }
            names.push(name);
            types.push(acorn_type);
        }
        for (name, acorn_type) in names.iter().zip(types.iter()) {
            stack.insert(name.to_string(), acorn_type.clone());
        }
        Ok((names, types))
    }

    // Errors if the value is not a constructor of the expected type.
    // Returns the index of which constructor this is, and the total number of constructors.
    fn expect_constructor(
        &self,
        project: &Project,
        expected_type: &AcornType,
        value: &AcornValue,
        source: &dyn ErrorSource,
    ) -> compilation::Result<(usize, usize)> {
        let info = match value.as_simple_constant() {
            Some((module, name)) => {
                let bindings = if module == self.module {
                    &self
                } else {
                    project
                        .get_bindings(module)
                        .ok_or_else(|| source.error("constructor module is unavailable"))?
                };
                bindings
                    .constant_info
                    .get(name)
                    .ok_or_else(|| source.error("constructor metadata is unavailable"))?
            }
            _ => return Err(source.error("invalid pattern")),
        };
        match &info.constructor {
            Some((constructor_type, i, total)) => {
                check_type(source, Some(expected_type), &constructor_type)?;
                Ok((*i, *total))
            }
            None => Err(source.error("expected a constructor")),
        }
    }

    // Evaluates a pattern match. Infers their types from the pattern.
    // Returns an error if the pattern is not a constructor of the expected type.
    // Returns:
    //   the constructor value
    //   a list of (name, type) pairs
    //   the index of which constructor this is
    //   the total number of constructors
    pub fn evaluate_pattern(
        &self,
        project: &Project,
        expected_type: &AcornType,
        pattern: &Expression,
    ) -> compilation::Result<(AcornValue, Vec<(String, AcornType)>, usize, usize)> {
        let (fn_exp, args) = match pattern {
            Expression::Apply(function, args) => (function, args),
            _ => {
                // This could be a no-argument constructor.
                let constructor = self.evaluate_value(project, pattern, None)?;
                let (i, total) =
                    self.expect_constructor(project, expected_type, &constructor, pattern)?;
                let pattern_type = constructor.get_type();
                if pattern_type.is_functional() {
                    return Err(pattern.error("constructor requires arguments"));
                }
                check_type(pattern, Some(expected_type), &pattern_type)?;

                return Ok((constructor, vec![], i, total));
            }
        };
        let constructor = self.evaluate_value(project, fn_exp, None)?;
        let (i, total) = self.expect_constructor(project, expected_type, &constructor, pattern)?;
        let fn_type = constructor.get_type();
        let arg_types = match fn_type {
            AcornType::Function(f) => {
                if &*f.return_type != expected_type {
                    return Err(pattern.error(&format!(
                        "the pattern has type {} but we are matching type {}",
                        &*f.return_type, expected_type
                    )));
                }
                f.arg_types
            }
            _ => return Err(fn_exp.error("expected a function")),
        };
        let name_exps = args.flatten_list(false)?;
        if name_exps.len() != arg_types.len() {
            return Err(args.error(&format!(
                "expected {} arguments but got {}",
                arg_types.len(),
                name_exps.len()
            )));
        }
        let mut args = vec![];
        for (name_exp, arg_type) in name_exps.into_iter().zip(arg_types) {
            let name = match name_exp {
                Expression::Singleton(token) if token.token_type == TokenType::Identifier => {
                    token.text().to_string()
                }
                _ => return Err(name_exp.error("expected a simple name in pattern")),
            };
            if self.name_in_use(&name) {
                return Err(name_exp.error(&format!("name '{}' is already bound", name)));
            }
            if args.iter().any(|(existing, _)| existing == &name) {
                return Err(name_exp.error("cannot use a name twice in one pattern"));
            }
            args.push((name, arg_type));
        }
        Ok((constructor, args, i, total))
    }

    // This function evaluates numbers when we already know what type they are.
    // token is the token to report errors with.
    // s is the string to parse.
    fn evaluate_number_with_type(
        &self,
        token: &Token,
        project: &Project,
        module: ModuleId,
        type_name: &str,
        s: &str,
    ) -> compilation::Result<AcornValue> {
        if let Some(potential) = self.evaluate_type_attribute(project, module, type_name, s) {
            return match potential {
                PotentialValue::Resolved(value) => Ok(value),
                PotentialValue::Unresolved(_) => {
                    Err(token.error(&format!("number {}.{} has unresolved type", type_name, s)))
                }
            };
        }

        if s.len() == 1 {
            return Err(token.error(&format!("digit {}.{} is not defined", type_name, s)));
        }

        let last_str = &s[s.len() - 1..];
        let last_num =
            self.evaluate_number_with_type(token, project, module, type_name, last_str)?;
        let initial_str = &s[..s.len() - 1];
        let initial_num =
            self.evaluate_number_with_type(token, project, module, type_name, initial_str)?;
        let read_fn = match self.evaluate_type_attribute(project, module, type_name, "read") {
            Some(PotentialValue::Resolved(value)) => value,
            Some(PotentialValue::Unresolved(_)) => {
                return Err(token.error(&format!(
                    "read function {}.read requires type arguments",
                    type_name
                )))
            }
            None => {
                return Err(token.error(&format!(
                    "{}.read must be defined to read numeric literals",
                    type_name
                )))
            }
        };
        let value = AcornValue::new_apply(read_fn, vec![initial_num, last_num]);
        Ok(value)
    }

    // Resolve canonical ownership without assuming that every loaded module has bindings.
    fn bindings_for_module<'a>(
        &'a self,
        project: &'a Project,
        module: ModuleId,
    ) -> Option<&'a BindingMap> {
        if module == self.module {
            Some(self)
        } else {
            project.get_bindings(module)
        }
    }

    // Evaluates a name scoped by a type name, like MyClass.foo
    fn evaluate_type_attribute(
        &self,
        project: &Project,
        module: ModuleId,
        type_name: &str,
        var_name: &str,
    ) -> Option<PotentialValue> {
        let bindings = self.bindings_for_module(project, module)?;
        let constant_name = format!("{}.{}", type_name, var_name);
        bindings.get_constant_value(&constant_name)
    }

    // Evaluates an expression that is supposed to describe a value, with an empty stack.
    pub fn evaluate_value(
        &self,
        project: &Project,
        expression: &Expression,
        expected_type: Option<&AcornType>,
    ) -> compilation::Result<AcornValue> {
        let value =
            self.evaluate_value_with_stack(&mut Stack::new(), project, expression, expected_type)?;
        check_type(expression, expected_type, &value.get_type())?;
        value
            .validate()
            .map_err(|message| expression.error(&message))?;
        Ok(value)
    }

    // Resolve an instance attribute using the canonical data or class identity.
    fn evaluate_instance_attribute(
        &self,
        source: &dyn ErrorSource,
        project: &Project,
        instance: AcornValue,
        name: &str,
    ) -> compilation::Result<AcornValue> {
        let base_type = instance.get_type();
        let (module, type_name) = match base_type {
            AcornType::Data(module, name, _) => (module, name),
            AcornType::Variable(param) | AcornType::Arbitrary(param) => {
                let class = param.typeclass.ok_or_else(|| {
                    source.error(&format!(
                        "unqualified type {} has no attributes",
                        param.name
                    ))
                })?;
                (class.module_id, class.name)
            }
            _ => {
                return Err(source.error(&format!(
                    "objects of type {:?} have no attributes",
                    base_type
                )))
            }
        };
        let bindings = self
            .bindings_for_module(project, module)
            .ok_or_else(|| source.error("could not load bindings for attribute module"))?;
        let constant_name = format!("{}.{}", type_name, name);
        let function = bindings
            .get_constant_value(&constant_name)
            .ok_or_else(|| source.error(&format!("unknown attribute '{}'", constant_name)))?;
        self.apply_potential(source, function, vec![instance], None)
    }

    // Evaluates a single name, which may be namespaced to another named entity.
    // In this situation, we don't know what sort of thing we expect the name to represent.
    // We have the entity described by a chain of names, and we're adding one more name to the chain.
    fn evaluate_name(
        &self,
        name_token: &Token,
        project: &Project,
        stack: &Stack,
        namespace: Option<NamedEntity>,
    ) -> compilation::Result<NamedEntity> {
        let name = name_token.text();
        match namespace {
            Some(NamedEntity::Unresolved(_)) => {
                Err(name_token.error("cannot access members of unresolved types"))
            }
            Some(NamedEntity::Value(instance)) => {
                let value =
                    self.evaluate_instance_attribute(name_token, project, instance, name)?;
                Ok(NamedEntity::Value(value))
            }
            Some(NamedEntity::Type(t)) => {
                if let AcornType::Variable(param) | AcornType::Arbitrary(param) = &t {
                    if let Some(class) = &param.typeclass {
                        let member = self
                            .evaluate_type_attribute(project, class.module_id, &class.name, name)
                            .ok_or_else(|| {
                                name_token.error(&format!(
                                    "{} has no attribute named '{}'",
                                    class.name, name
                                ))
                            })?;
                        return match member {
                            PotentialValue::Resolved(value) => Ok(NamedEntity::Value(value)),
                            PotentialValue::Unresolved(unresolved) => Ok(NamedEntity::Value(
                                unresolved.resolve(name_token, vec![t], &self.proof_scope)?,
                            )),
                        };
                    }
                }
                if let AcornType::Data(module, type_name, actuals) = t {
                    if name_token.token_type == TokenType::Numeral {
                        if !actuals.is_empty() {
                            return Err(
                                name_token.error("numeric literals cannot have type parameters")
                            );
                        }
                        let value = self.evaluate_number_with_type(
                            name_token,
                            project,
                            module,
                            &type_name,
                            name_token.text(),
                        )?;
                        return Ok(NamedEntity::Value(value));
                    }
                    let attribute = self.evaluate_type_attribute(project, module, &type_name, name);
                    let owner = self.bindings_for_module(project, module);
                    let scope = owner.and_then(|bindings| {
                        bindings
                            .instance_scopes
                            .iter()
                            .find(|((target, class), _)| target == &type_name && class.name == name)
                            .map(|(_, scope)| scope)
                    });
                    if let Some(scope) = scope {
                        if attribute.is_some() {
                            return Err(
                                name_token.error("ambiguous type attribute and instance namespace")
                            );
                        }
                        if !actuals.is_empty() {
                            return Err(name_token
                                .error("concrete instance namespace cannot have type parameters"));
                        }
                        return Ok(NamedEntity::Instance(module, scope.clone()));
                    }
                    match attribute {
                        Some(PotentialValue::Resolved(value)) => {
                            if !actuals.is_empty() {
                                return Err(
                                    name_token.error("member does not accept type parameters")
                                );
                            }
                            Ok(NamedEntity::Value(value))
                        }
                        Some(PotentialValue::Unresolved(unresolved)) => {
                            if actuals.is_empty() {
                                Ok(NamedEntity::Unresolved(unresolved))
                            } else {
                                Ok(NamedEntity::Value(unresolved.resolve(
                                    name_token,
                                    actuals,
                                    &self.proof_scope,
                                )?))
                            }
                        }
                        None => Err(name_token
                            .error(&format!("{} has no member named '{}'", type_name, name))),
                    }
                } else {
                    Err(name_token.error("expected a data type"))
                }
            }
            Some(NamedEntity::UnresolvedType(t)) => self
                .evaluate_type_attribute(project, t.module_id, &t.name, name)
                .map(PotentialValue::to_named_entity)
                .ok_or_else(|| {
                    name_token.error(&format!("{} has no member named '{}'", t.name, name))
                }),
            Some(NamedEntity::Typeclass(class)) => self
                .evaluate_type_attribute(project, class.module_id, &class.name, name)
                .map(PotentialValue::to_named_entity)
                .ok_or_else(|| {
                    name_token.error(&format!("{} has no attribute named '{}'", class.name, name))
                }),
            Some(NamedEntity::Instance(module, scope)) => self
                .evaluate_type_attribute(project, module, &scope, name)
                .map(PotentialValue::to_named_entity)
                .ok_or_else(|| {
                    name_token.error(&format!(
                        "instance {} has no member named '{}'",
                        scope, name
                    ))
                }),
            Some(NamedEntity::Module(module)) => {
                if let Some(bindings) = project.get_bindings(module) {
                    bindings.evaluate_name(name_token, project, &Stack::new(), None)
                } else {
                    Err(name_token.error("could not load bindings for module"))
                }
            }
            None => {
                match name_token.token_type {
                    TokenType::Identifier => {
                        if self.is_module(name) {
                            match self.name_to_module.get(name) {
                                Some(module) => Ok(NamedEntity::Module(*module)),
                                None => Err(name_token.error("unknown module")),
                            }
                        } else if self.has_type_name(name) {
                            match self.get_potential_type_for_name(name) {
                                Some(PotentialType::Resolved(t)) => {
                                    Ok(NamedEntity::Type(t.clone()))
                                }
                                Some(PotentialType::Unresolved(t)) => {
                                    Ok(NamedEntity::UnresolvedType(t.clone()))
                                }
                                None => Err(name_token.error("unknown type")),
                            }
                        } else if let Some(class) = self.get_typeclass_for_name(name) {
                            Ok(NamedEntity::Typeclass(class.clone()))
                        } else if let Some((i, t)) = stack.get(name) {
                            // This is a stack variable
                            Ok(NamedEntity::Value(AcornValue::Variable(*i, t.clone())))
                        } else if let Some(potential) = self.get_constant_value(name) {
                            Ok(potential.to_named_entity())
                        } else {
                            Err(name_token.error(&format!("unknown identifier '{}'", name)))
                        }
                    }
                    TokenType::Numeral => {
                        let (module, type_name) = match &self.default {
                            Some((module, type_name)) => (module, type_name),
                            None => {
                                return Err(name_token
                                    .error("you must set a default type for numeric literals"));
                            }
                        };
                        let value = self.evaluate_number_with_type(
                            name_token,
                            project,
                            *module,
                            type_name,
                            name_token.text(),
                        )?;
                        Ok(NamedEntity::Value(value))
                    }
                    TokenType::SelfToken => {
                        if let Some((i, t)) = stack.get(name) {
                            // This is a stack variable
                            Ok(NamedEntity::Value(AcornValue::Variable(*i, t.clone())))
                        } else {
                            Err(name_token.error("unexpected location for 'self'"))
                        }
                    }
                    t => Err(name_token.error(&format!("unexpected {:?} token", t))),
                }
            }
        }
    }

    // Evaluates a single dot operator.
    fn evaluate_dot_expression(
        &self,
        stack: &mut Stack,
        project: &Project,
        left: &Expression,
        right: &Expression,
    ) -> compilation::Result<NamedEntity> {
        let right_token = match right {
            Expression::Singleton(token) => token,
            _ => return Err(right.error("expected an identifier after a dot")),
        };
        let left_entity = self.evaluate_entity(stack, project, left)?;

        self.evaluate_name(right_token, project, stack, Some(left_entity))
    }

    // Evaluates an expression that could represent any sort of named entity.
    // It could be a type, a value, or a module.
    fn evaluate_entity(
        &self,
        stack: &mut Stack,
        project: &Project,
        expression: &Expression,
    ) -> compilation::Result<NamedEntity> {
        // Handle a plain old name
        if let Expression::Singleton(token) = expression {
            return self.evaluate_name(token, project, stack, None);
        }

        if let Expression::Binary(left, token, right) = expression {
            if token.token_type == TokenType::Dot {
                return self.evaluate_dot_expression(stack, project, left, right);
            }
        }

        // Resolve the head by its binding, rather than guessing from capitalization.
        // A type application can be the namespace of a subsequent member lookup.
        if let Expression::Apply(head, arguments) = expression {
            if let Expression::Grouping(opening, inner, _) = arguments.as_ref() {
                if opening.token_type == TokenType::LessThan {
                    let potential = match self.evaluate_entity(stack, project, head)? {
                        NamedEntity::Type(t) => Some(PotentialType::Resolved(t)),
                        NamedEntity::UnresolvedType(t) => Some(PotentialType::Unresolved(t)),
                        _ => None,
                    };
                    if let Some(potential) = potential {
                        let actuals = inner
                            .flatten_comma_separated_list()
                            .into_iter()
                            .map(|arg| self.evaluate_type(project, arg))
                            .collect::<compilation::Result<Vec<_>>>()?;
                        return Ok(NamedEntity::Type(potential.resolve_in_scope(
                            actuals,
                            expression,
                            &self.proof_scope,
                        )?));
                    }
                }
            }
        }

        // All remaining expressions must be values.
        let value = self.evaluate_value_with_stack(stack, project, expression, None)?;
        Ok(NamedEntity::Value(value))
    }

    // Evaluates an infix operator.
    // name is the special alphanumeric name that corresponds to the operator, like "+" expands to "add".
    fn evaluate_infix(
        &self,
        stack: &mut Stack,
        project: &Project,
        expression: &Expression,
        left: &Expression,
        token: &Token,
        right: &Expression,
        name: &str,
        expected_type: Option<&AcornType>,
    ) -> compilation::Result<AcornValue> {
        let left_value = self.evaluate_value_with_stack(stack, project, left, None)?;
        let right_value = self.evaluate_value_with_stack(stack, project, right, None)?;

        // Get the partial application to the left
        let partial = self.evaluate_instance_attribute(expression, project, left_value, name)?;
        let mut fa = match partial {
            AcornValue::Application(fa) => fa,
            _ => {
                return Err(expression.error(&format!(
                    "the '{}' operator requires a method named '{}'",
                    token, name
                )))
            }
        };
        match fa.function.get_type() {
            AcornType::Function(f) => {
                if f.arg_types.len() != 2 {
                    return Err(expression
                        .error(&format!("expected a binary function for '{}' method", name)));
                }
                check_type(expression, Some(&f.arg_types[1]), &right_value.get_type())?;
            }
            _ => return Err(expression.error(&format!("unexpected type for '{}' method", name))),
        };

        fa.args.push(right_value);
        let value = AcornValue::new_apply(*fa.function, fa.args);
        check_type(expression, expected_type, &value.get_type())?;
        Ok(value)
    }

    // Imports a name from another module.
    // The name could either be a type or a value.
    pub fn import_name(
        &mut self,
        project: &Project,
        module: ModuleId,
        name_token: &Token,
    ) -> compilation::Result<()> {
        if self.name_in_use(&name_token.text()) {
            return Err(name_token.error(&format!(
                "name {} already bound in this module",
                name_token.text()
            )));
        }
        let bindings = match project.get_bindings(module) {
            Some(b) => b,
            None => {
                return Err(
                    name_token.error(&format!("could not load bindings for imported module"))
                )
            }
        };
        let entity = bindings.evaluate_name(name_token, project, &Stack::new(), None)?;
        match entity {
            NamedEntity::Value(value) => {
                // Add a local alias that mirrors this constant's name in the imported module.
                if let Some((ext_module, ext_name)) = value.as_simple_constant() {
                    self.add_alias(
                        name_token.text(),
                        ext_module,
                        ext_name.to_string(),
                        PotentialValue::Resolved(value),
                    );
                } else {
                    return Err(name_token.error("cannot import non-constant values"));
                }
                Ok(())
            }
            NamedEntity::Type(acorn_type) => {
                if let AcornType::Data(owner, _, _) = &acorn_type {
                    if let Some(bindings) = project.get_bindings(*owner) {
                        self.import_instance_members(bindings);
                    }
                }
                self.add_type_alias(&name_token.text(), acorn_type);
                Ok(())
            }
            NamedEntity::Unresolved(unresolved) => {
                self.add_alias(
                    name_token.text(),
                    unresolved.module_id,
                    unresolved.name.clone(),
                    PotentialValue::Unresolved(unresolved),
                );
                Ok(())
            }
            NamedEntity::UnresolvedType(t) => {
                self.add_potential_type_alias(name_token.text(), PotentialType::Unresolved(t));
                Ok(())
            }
            NamedEntity::Instance(..) => {
                Err(name_token.error("cannot import instance namespaces indirectly"))
            }
            NamedEntity::Module(_) => Err(name_token.error("cannot import modules indirectly")),
            NamedEntity::Typeclass(_) => {
                Err(name_token.error("cannot import typeclasses indirectly"))
            }
        }
    }

    pub fn apply_potential(
        &self,
        source: &dyn ErrorSource,
        potential: PotentialValue,
        args: Vec<AcornValue>,
        expected_type: Option<&AcornType>,
    ) -> compilation::Result<AcornValue> {
        match potential {
            PotentialValue::Resolved(function) => {
                self.apply_resolved(source, function, args, expected_type)
            }
            PotentialValue::Unresolved(unresolved) => {
                self.resolve_function(source, unresolved, args, &[], expected_type)
            }
        }
    }

    fn apply_resolved(
        &self,
        source: &dyn ErrorSource,
        function: AcornValue,
        args: Vec<AcornValue>,
        expected_type: Option<&AcornType>,
    ) -> compilation::Result<AcornValue> {
        if !args.is_empty() {
            let AcornType::Function(ft) = function.get_type() else {
                return Err(source.error("expected a function"));
            };
            if args.len() > ft.arg_types.len() {
                return Err(source.error(&format!(
                    "expected <= {} arguments, but got {}",
                    ft.arg_types.len(),
                    args.len()
                )));
            }
            for (arg, expected) in args.iter().zip(&ft.arg_types) {
                check_type(source, Some(expected), &arg.get_type())?;
            }
        }
        let value = AcornValue::new_apply(function, args);
        check_type(source, expected_type, &value.get_type())?;
        Ok(value)
    }

    // Apply a pending declaration while keeping its ordered actuals and source argument ranges.
    fn resolve_function(
        &self,
        source: &dyn ErrorSource,
        unresolved: UnresolvedConstant,
        args: Vec<AcornValue>,
        arg_sources: &[&Expression],
        expected_type: Option<&AcornType>,
    ) -> compilation::Result<AcornValue> {
        let function_type = match &unresolved.generic_type {
            AcornType::Function(ft) => ft,
            _ => return Err(source.error("expected a function")),
        };
        if args.len() > function_type.arg_types.len() {
            return Err(source.error(&format!(
                "expected <= {} arguments, but got {}",
                function_type.arg_types.len(),
                args.len()
            )));
        }
        if unresolved.generic_type.has_arbitrary() {
            return Err(source.error("generic function cannot capture arbitrary types"));
        }
        let mut mapping = HashMap::new();
        for (i, (arg, expected)) in args.iter().zip(&function_type.arg_types).enumerate() {
            if !expected.match_instance_in_scope(&arg.get_type(), &mut mapping, &self.proof_scope) {
                let arg_source: &dyn ErrorSource = arg_sources.get(i).map_or(source, |expr| *expr);
                return Err(arg_source.error(&format!(
                    "expected type {}, but got {}",
                    expected,
                    arg.get_type()
                )));
            }
        }
        let actuals = unresolved
            .params
            .iter()
            .map(|formal| {
                mapping.get(&formal.name).cloned().ok_or_else(|| {
                    source.error(&format!("parameter {} could not be inferred", formal.name))
                })
            })
            .collect::<compilation::Result<Vec<_>>>()?;
        let instance = unresolved.resolve(source, actuals, &self.proof_scope)?;
        self.apply_resolved(source, instance, args, expected_type)
    }

    fn infer_and_apply(
        &self,
        stack: &mut Stack,
        project: &Project,
        source: &dyn ErrorSource,
        unresolved: UnresolvedConstant,
        arg_exprs: Vec<&Expression>,
        expected_type: Option<&AcornType>,
    ) -> compilation::Result<AcornValue> {
        let AcornType::Function(ft) = &unresolved.generic_type else {
            return Err(source.error("expected a function"));
        };
        if arg_exprs.len() > ft.arg_types.len() {
            return Err(source.error(&format!(
                "expected <= {} arguments, but got {}",
                ft.arg_types.len(),
                arg_exprs.len()
            )));
        }
        let args = arg_exprs
            .iter()
            .map(|expr| self.evaluate_value_with_stack(stack, project, expr, None))
            .collect::<compilation::Result<Vec<_>>>()?;
        self.resolve_function(source, unresolved, args, &arg_exprs, expected_type)
    }

    // Evaluate a completed value; unresolved declarations cannot enter nested proof expressions.
    pub fn evaluate_value_with_stack(
        &self,
        stack: &mut Stack,
        project: &Project,
        expression: &Expression,
        expected_type: Option<&AcornType>,
    ) -> compilation::Result<AcornValue> {
        let value = self
            .evaluate_potential_value(stack, project, expression, expected_type)?
            .value(expression)?;
        check_type(expression, expected_type, &value.get_type())?;
        Ok(value)
    }

    // Evaluates an expression that describes a value, with a stack given as context.
    // Only function heads may carry pending generic arguments.
    fn evaluate_potential_value(
        &self,
        stack: &mut Stack,
        project: &Project,
        expression: &Expression,
        expected_type: Option<&AcornType>,
    ) -> compilation::Result<PotentialValue> {
        let value = match expression {
            Expression::Singleton(token) => match token.token_type {
                TokenType::Axiom => {
                    Err(token.error("axiom is only allowed as a complete declaration value"))
                }
                TokenType::ForAll | TokenType::Exists | TokenType::Function => {
                    return Err(token.error("binder keywords cannot be used as values"));
                }
                TokenType::True | TokenType::False => {
                    check_type(token, expected_type, &AcornType::Bool)?;
                    Ok(AcornValue::Bool(token.token_type == TokenType::True))
                }
                TokenType::Identifier | TokenType::Numeral | TokenType::SelfToken => {
                    let entity = self.evaluate_name(token, project, stack, None)?;
                    return entity.expect_potential_value(expected_type, expression);
                }
                token_type => Err(token.error(&format!(
                    "identifier expression has token type {:?}",
                    token_type
                ))),
            },
            Expression::Unary(token, expr) => match token.token_type {
                TokenType::Not => {
                    check_type(expression, expected_type, &AcornType::Bool)?;
                    let value = self.evaluate_value_with_stack(
                        stack,
                        project,
                        expr,
                        Some(&AcornType::Bool),
                    )?;
                    Ok(AcornValue::Not(Box::new(value)))
                }

                operator => {
                    let name = operator.to_prefix_magic_method_name().ok_or_else(|| {
                        token.error("unexpected unary operator in value expression")
                    })?;
                    let operand = self.evaluate_value_with_stack(stack, project, expr, None)?;
                    let value = self.evaluate_instance_attribute(token, project, operand, name)?;
                    check_type(token, expected_type, &value.get_type())?;
                    Ok(value)
                }
            },
            Expression::Binary(left, token, right) => match token.token_type {
                TokenType::RightArrow | TokenType::Implies => {
                    check_type(expression, expected_type, &AcornType::Bool)?;
                    let left_value = self.evaluate_value_with_stack(
                        stack,
                        project,
                        left,
                        Some(&AcornType::Bool),
                    )?;
                    let right_value = self.evaluate_value_with_stack(
                        stack,
                        project,
                        right,
                        Some(&AcornType::Bool),
                    )?;

                    Ok(AcornValue::Binary(
                        BinaryOp::Implies,
                        Box::new(left_value),
                        Box::new(right_value),
                    ))
                }
                TokenType::Equals => {
                    check_type(expression, expected_type, &AcornType::Bool)?;
                    let left_value = self.evaluate_value_with_stack(stack, project, left, None)?;
                    let right_value = self.evaluate_value_with_stack(
                        stack,
                        project,
                        right,
                        Some(&left_value.get_type()),
                    )?;
                    Ok(AcornValue::Binary(
                        BinaryOp::Equals,
                        Box::new(left_value),
                        Box::new(right_value),
                    ))
                }
                TokenType::NotEquals => {
                    check_type(expression, expected_type, &AcornType::Bool)?;
                    let left_value = self.evaluate_value_with_stack(stack, project, left, None)?;
                    let right_value = self.evaluate_value_with_stack(
                        stack,
                        project,
                        right,
                        Some(&left_value.get_type()),
                    )?;
                    Ok(AcornValue::Binary(
                        BinaryOp::NotEquals,
                        Box::new(left_value),
                        Box::new(right_value),
                    ))
                }
                TokenType::And => {
                    check_type(expression, expected_type, &AcornType::Bool)?;
                    let left_value = self.evaluate_value_with_stack(
                        stack,
                        project,
                        left,
                        Some(&AcornType::Bool),
                    )?;
                    let right_value = self.evaluate_value_with_stack(
                        stack,
                        project,
                        right,
                        Some(&AcornType::Bool),
                    )?;
                    Ok(AcornValue::Binary(
                        BinaryOp::And,
                        Box::new(left_value),
                        Box::new(right_value),
                    ))
                }
                TokenType::Or => {
                    check_type(expression, expected_type, &AcornType::Bool)?;
                    let left_value = self.evaluate_value_with_stack(
                        stack,
                        project,
                        left,
                        Some(&AcornType::Bool),
                    )?;
                    let right_value = self.evaluate_value_with_stack(
                        stack,
                        project,
                        right,
                        Some(&AcornType::Bool),
                    )?;
                    Ok(AcornValue::Binary(
                        BinaryOp::Or,
                        Box::new(left_value),
                        Box::new(right_value),
                    ))
                }
                TokenType::Dot => {
                    let entity = self.evaluate_dot_expression(stack, project, left, right)?;
                    return entity.expect_potential_value(expected_type, expression);
                }
                token_type => match token_type.to_infix_magic_method_name() {
                    Some(name) => self.evaluate_infix(
                        stack,
                        project,
                        expression,
                        left,
                        token,
                        right,
                        name,
                        expected_type,
                    ),
                    None => Err(expression.error(&format!(
                        "unexpected operator '{}' in value expression",
                        token
                    ))),
                },
            },
            Expression::Apply(function_expr, args_expr) => {
                let function =
                    self.evaluate_potential_value(stack, project, function_expr, None)?;
                let arg_exprs = match args_expr.as_ref() {
                    Expression::Grouping(delimiter, arguments, _) => {
                        let arguments = arguments.flatten_comma_separated_list();
                        if delimiter.token_type == TokenType::LessThan {
                            let PotentialValue::Unresolved(unresolved) = function else {
                                return Err(args_expr.error("unexpected type argument list"));
                            };
                            if arguments.len() != unresolved.params.len() {
                                return Err(args_expr.error(&format!(
                                    "expected {} type arguments, but got {}",
                                    unresolved.params.len(),
                                    arguments.len()
                                )));
                            }
                            let actual_arguments = arguments
                                .into_iter()
                                .map(|argument| self.evaluate_type(project, argument))
                                .collect::<compilation::Result<Vec<_>>>()?;
                            let instance = unresolved.resolve(
                                args_expr.as_ref(),
                                actual_arguments,
                                &self.proof_scope,
                            )?;
                            check_type(expression, expected_type, &instance.get_type())?;
                            return Ok(PotentialValue::Resolved(instance));
                        }
                        arguments
                    }
                    _ => return Err(args_expr.error("expected a grouped argument list")),
                };
                let function_type = match function.get_type() {
                    AcornType::Function(function) => function,
                    _ => return Err(function_expr.error("expected a function")),
                };

                if function_type.arg_types.len() < arg_exprs.len() {
                    return Err(args_expr.error(&format!(
                        "expected <= {} arguments, but got {}",
                        function_type.arg_types.len(),
                        arg_exprs.len()
                    )));
                }

                let function = match function {
                    PotentialValue::Unresolved(unresolved) => {
                        return self
                            .infer_and_apply(
                                stack,
                                project,
                                &**function_expr,
                                unresolved,
                                arg_exprs,
                                expected_type,
                            )
                            .map(PotentialValue::Resolved);
                    }
                    PotentialValue::Resolved(function) => function,
                };

                // Ordinary functions keep the types declared in their current scope.
                let mut args = vec![];
                for (i, arg_expr) in arg_exprs.iter().enumerate() {
                    let arg_type = &function_type.arg_types[i];
                    let arg =
                        self.evaluate_value_with_stack(stack, project, arg_expr, Some(arg_type))?;
                    // Some expression forms do not use the expectation while evaluating.
                    // Enforce the argument type at the application boundary as well.
                    check_type(*arg_expr, Some(arg_type), &arg.get_type())?;
                    args.push(arg);
                }
                check_type(
                    &**function_expr,
                    expected_type,
                    &function_type.applied_type(args.len()),
                )?;
                Ok(AcornValue::new_apply(function, args))
            }
            Expression::Grouping(_, e, _) => {
                return self.evaluate_potential_value(stack, project, e, expected_type);
            }
            Expression::Binder(token, args, body, _) => {
                if args.len() < 1 {
                    return Err(token.error("binders must have at least one argument"));
                }
                let (arg_names, arg_types) = self.bind_args(stack, project, args, None)?;
                let body_type = match token.token_type {
                    TokenType::ForAll => Some(&AcornType::Bool),
                    TokenType::Exists => Some(&AcornType::Bool),
                    _ => None,
                };
                let ret_val = match self.evaluate_value_with_stack(stack, project, body, body_type)
                {
                    Ok(value) => match token.token_type {
                        TokenType::ForAll => Ok(AcornValue::ForAll(arg_types, Box::new(value))),
                        TokenType::Exists => Ok(AcornValue::Exists(arg_types, Box::new(value))),
                        TokenType::Function => Ok(AcornValue::Lambda(arg_types, Box::new(value))),
                        _ => Err(token.error("expected a binder identifier token")),
                    },
                    Err(e) => Err(e),
                };
                stack.remove_all(&arg_names);
                if ret_val.is_ok()
                    && token.token_type == TokenType::Function
                    && expected_type.is_some()
                {
                    // We could check this before creating the value rather than afterwards.
                    // It seems theoretically faster but I'm not sure if there's any reason to.
                    check_type(token, expected_type, &ret_val.as_ref().unwrap().get_type())?;
                }
                ret_val
            }
            Expression::IfThenElse(_, cond_exp, if_exp, else_exp, _) => {
                let cond = self.evaluate_value_with_stack(
                    stack,
                    project,
                    cond_exp,
                    Some(&AcornType::Bool),
                )?;
                let if_value =
                    self.evaluate_value_with_stack(stack, project, if_exp, expected_type)?;
                let else_value = self.evaluate_value_with_stack(
                    stack,
                    project,
                    else_exp,
                    Some(&if_value.get_type()),
                )?;
                Ok(AcornValue::IfThenElse(
                    Box::new(cond),
                    Box::new(if_value),
                    Box::new(else_value),
                ))
            }
            Expression::Match(_, scrutinee_exp, case_exps, _) => {
                let scrutinee =
                    self.evaluate_value_with_stack(stack, project, scrutinee_exp, None)?;
                let scrutinee_type = scrutinee.get_type();
                let mut cases = vec![];
                let mut result_type = expected_type.cloned();
                let mut indices = vec![];
                let mut all_cases = false;
                for (pattern_exp, result_exp) in case_exps {
                    let (_, args, i, total) =
                        self.evaluate_pattern(project, &scrutinee_type, pattern_exp)?;
                    // Check every outer-scope conflict before binding any case locals.
                    for (name, _) in &args {
                        if stack.get(name).is_some() {
                            return Err(pattern_exp.error(&format!("name {} already bound", name)));
                        }
                    }
                    if indices.contains(&i) {
                        return Err(pattern_exp
                            .error("cannot have multiple cases for the same constructor"));
                    }
                    indices.push(i);
                    if total == indices.len() {
                        all_cases = true;
                    }
                    for (name, arg_type) in &args {
                        stack.insert(name.clone(), arg_type.clone());
                    }
                    let evaluated = (|| {
                        let pattern =
                            self.evaluate_value_with_stack(stack, project, pattern_exp, None)?;
                        let result = self.evaluate_value_with_stack(
                            stack,
                            project,
                            result_exp,
                            result_type.as_ref(),
                        )?;
                        Ok::<_, Error>((pattern, result))
                    })();
                    let mut arg_types = Vec::with_capacity(args.len());
                    for (name, arg_type) in args {
                        stack.remove(&name);
                        arg_types.push(arg_type);
                    }
                    let (pattern, result) = evaluated?;
                    if result_type.is_none() {
                        result_type = Some(result.get_type());
                    }
                    cases.push((arg_types, pattern, result));
                }
                if !all_cases {
                    return Err(expression.error("not all constructors are covered in this match"));
                }
                Ok(AcornValue::Match(Box::new(scrutinee), cases))
            }
        }?;
        Ok(PotentialValue::Resolved(value))
    }

    pub(crate) fn evaluate_typeclass(
        &self,
        project: &Project,
        expression: &Expression,
    ) -> compilation::Result<Typeclass> {
        match self.evaluate_entity(&mut Stack::new(), project, expression)? {
            NamedEntity::Typeclass(class) => Ok(class),
            _ => Err(expression.error("expected a typeclass")),
        }
    }

    // Validate a complete parameter list before introducing any temporary bindings.
    // Bounds retain the canonical typeclass identity and declaration order.
    pub fn evaluate_type_params(
        &self,
        project: &Project,
        expressions: &[TypeParamExpr],
    ) -> compilation::Result<Vec<TypeParam>> {
        let mut seen = HashSet::with_capacity(expressions.len());
        let mut params = Vec::with_capacity(expressions.len());
        for expression in expressions {
            let name = expression.name.text();
            if self.name_in_use(name) {
                return Err(expression
                    .name
                    .error("type parameter already defined in this scope"));
            }
            if !seen.insert(name) {
                return Err(expression.name.error("duplicate type parameter"));
            }
            let typeclass = expression
                .typeclass
                .as_ref()
                .map(|bound| self.evaluate_typeclass(project, bound))
                .transpose()?;
            params.push(TypeParam {
                name: name.to_string(),
                typeclass,
            });
        }
        Ok(params)
    }

    // Evaluate an expression that creates a new scope for the value inside it.
    // It has declarations, introducing new variables and types that exist just for this value,
    // and it has the value itself, which can use those declarations.
    //
    // type_params is a list of tokens for the generic types introduced for this scope.
    // args is a list of the new variables declared for this scope.
    // value_type_expr is an optional expression for the type of the value.
    //   (None means expect a boolean value.)
    // value_expr is the expression for the value itself.
    //
    // Evaluates in an isolated temporary scope, leaving these bindings unchanged on every path.
    //
    // Returns a tuple with:
    //   a list of type parameter names
    //   a list of argument names
    //   a list of argument types
    //   an optional unbound value. (None means axiom.)
    //   the value type
    //
    // Generic parameters in the argument and value types are represented by type variables.
    // class_type should be provided if this is the definition of a member function.
    //
    // The return value is "unbound" in the sense that it has variable atoms that are not
    // bound within any lambda, exists, or forall value.
    pub fn evaluate_scoped_value(
        &mut self,
        project: &Project,
        type_params: &[TypeParamExpr],
        args: &[Declaration],
        value_type_expr: Option<&Expression>,
        value_expr: &Expression,
        class_type: Option<&AcornType>,
        function_name: Option<&str>,
    ) -> compilation::Result<(
        Vec<TypeParam>,
        Vec<String>,
        Vec<AcornType>,
        Option<AcornValue>,
        AcornType,
    )> {
        let mut scope = self.clone();
        scope.evaluate_scoped_value_in_scope(
            project,
            type_params,
            args,
            value_type_expr,
            value_expr,
            class_type,
            function_name,
        )
    }

    fn evaluate_scoped_value_in_scope(
        &mut self,
        project: &Project,
        type_params: &[TypeParamExpr],
        args: &[Declaration],
        value_type_expr: Option<&Expression>,
        value_expr: &Expression,
        class_type: Option<&AcornType>,
        function_name: Option<&str>,
    ) -> compilation::Result<(
        Vec<TypeParam>,
        Vec<String>,
        Vec<AcornType>,
        Option<AcornValue>,
        AcornType,
    )> {
        // Bind only after the entire list and its bounds have been validated.
        let type_param_names = self.evaluate_type_params(project, type_params)?;
        for param in &type_param_names {
            self.add_type_variable(&param.name, param.typeclass.clone());
        }
        let mut stack = Stack::new();
        let (arg_names, arg_types) = self.bind_args(&mut stack, project, args, class_type)?;

        if let Some(name) = function_name {
            if self.name_in_use(name) {
                return Err(value_expr.error("function name conflicts with a type parameter"));
            }
        }

        // Evaluate the inner value using our modified bindings
        let value_type = match value_type_expr {
            Some(e) => self.evaluate_type(project, e)?,
            None => AcornType::Bool,
        };
        if !type_param_names.is_empty()
            && (arg_types.iter().any(AcornType::has_arbitrary) || value_type.has_arbitrary())
        {
            return Err(
                value_expr.error("generic declarations cannot capture outer arbitrary types")
            );
        }
        if let Some(name) = function_name {
            let function_type = AcornType::new_functional(arg_types.clone(), value_type.clone());
            self.add_constant(name, type_param_names.clone(), function_type, None, None);
        }
        let value = if value_expr.is_axiom() {
            None
        } else {
            let value =
                self.evaluate_value_with_stack(&mut stack, project, value_expr, Some(&value_type))?;
            if let Some(name) = function_name {
                let mut checker =
                    TerminationChecker::new(self.module, name.to_string(), arg_types.len());
                if !checker.check(&value) {
                    return Err(value_expr
                        .error("the termination checker could not prove that this terminates"));
                }
            }
            check_type(value_expr, Some(&value_type), &value.get_type())?;
            AcornValue::new_lambda(arg_types.clone(), value.clone())
                .validate()
                .map_err(|message| value_expr.error(&message))?;
            Some(value)
        };

        if !type_param_names.is_empty() && value.as_ref().is_some_and(AcornValue::has_arbitrary) {
            return Err(
                value_expr.error("generic declarations cannot capture outer arbitrary types")
            );
        }
        Ok((type_param_names, arg_names, arg_types, value, value_type))
    }

    // Finds the names of all constants that are in this module but unknown to this binding map.
    // Scoped polymorphic definitions cannot be represented by one exported variable.
    pub fn find_unknown_local_constants(
        &self,
        value: &AcornValue,
        answer: &mut HashMap<String, AcornType>,
    ) -> Result<(), String> {
        match value {
            AcornValue::Variable(_, _) | AcornValue::Bool(_) => {}
            AcornValue::Constant(c) => {
                if c.module_id == self.module && !self.constant_info.contains_key(&c.name) {
                    if !c.params.is_empty() {
                        return Err(format!(
                            "cannot export scoped generic constant '{}' from this block",
                            c.name
                        ));
                    }
                    answer.insert(c.name.to_string(), c.instance_type.clone());
                }
            }

            AcornValue::Application(app) => {
                self.find_unknown_local_constants(&app.function, answer)?;
                for arg in &app.args {
                    self.find_unknown_local_constants(arg, answer)?;
                }
            }
            AcornValue::Lambda(_, value)
            | AcornValue::ForAll(_, value)
            | AcornValue::Exists(_, value) => {
                self.find_unknown_local_constants(value, answer)?;
            }
            AcornValue::Binary(_, left, right) => {
                self.find_unknown_local_constants(left, answer)?;
                self.find_unknown_local_constants(right, answer)?;
            }
            AcornValue::IfThenElse(cond, then_value, else_value) => {
                self.find_unknown_local_constants(cond, answer)?;
                self.find_unknown_local_constants(then_value, answer)?;
                self.find_unknown_local_constants(else_value, answer)?;
            }
            AcornValue::Match(scrutinee, cases) => {
                self.find_unknown_local_constants(scrutinee, answer)?;
                for (_, pattern, result) in cases {
                    self.find_unknown_local_constants(pattern, answer)?;
                    self.find_unknown_local_constants(result, answer)?;
                }
            }
            AcornValue::Not(value) => {
                self.find_unknown_local_constants(value, answer)?;
            }
        }
        Ok(())
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Tools for going the other way, to create expressions and code strings from values and types.
    ////////////////////////////////////////////////////////////////////////////////

    // Returns an error if this type can't be encoded. For example, it could be a type that
    // is not obviously accessible from this scope.
    fn type_to_expr(&self, acorn_type: &AcornType) -> Result<Expression, CodeGenError> {
        if let AcornType::Function(ft) = acorn_type {
            let mut args = vec![];
            for arg_type in &ft.arg_types {
                args.push(self.type_to_expr(arg_type)?);
            }
            let lhs = if args.len() == 1 && !matches!(ft.arg_types[0], AcornType::Function(_)) {
                args.pop().unwrap()
            } else {
                Expression::generate_grouping(args)
            };
            let rhs = self.type_to_expr(&ft.return_type)?;
            return Ok(Expression::Binary(
                Box::new(lhs),
                TokenType::RightArrow.generate(),
                Box::new(rhs),
            ));
        }

        if let Some(name) = self.type_to_typename.get(acorn_type) {
            return Ok(Expression::generate_identifier(name));
        }
        if let AcornType::Data(module, type_name, actuals) = acorn_type {
            let family = (*module, type_name.clone(), actuals.len());
            if let Some(alias) = self.generic_type_aliases.get(&family) {
                return self.parametrize_type_expr(Expression::generate_identifier(alias), actuals);
            }
            let head = if *module == self.module && self.has_type_name(type_name) {
                Some(Expression::generate_identifier(type_name))
            } else {
                self.module_to_name.get(module).map(|module_name| {
                    Expression::generate_identifier_chain(&[module_name, type_name])
                })
            };
            if let Some(head) = head {
                return self.parametrize_type_expr(head, actuals);
            }
        }
        Err(CodeGenError::unnamed_type(acorn_type))
    }

    fn parametrize_type_expr(
        &self,
        head: Expression,
        actuals: &[AcornType],
    ) -> Result<Expression, CodeGenError> {
        if actuals.is_empty() {
            return Ok(head);
        }
        let arguments = actuals
            .iter()
            .map(|t| self.type_to_expr(t))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Expression::Apply(
            Box::new(head),
            Box::new(Expression::generate_type_arguments(arguments)),
        ))
    }

    // We use variables named x0, x1, x2, etc when new temporary variables are needed.
    // Find the next one that's available.
    fn next_x_var(&self, next_x: &mut u32) -> String {
        loop {
            let name = format!("x{}", next_x);
            *next_x += 1;
            if !self.name_in_use(&name) {
                return name;
            }
        }
    }

    // We use variables named k0, k1, k2, etc when new constant names are needed.
    // Find the next one that's available.
    fn next_k_var(&self, next_k: &mut u32) -> String {
        loop {
            let name = format!("k{}", next_k);
            *next_k += 1;
            if !self.name_in_use(&name) {
                return name;
            }
        }
    }

    // If this value cannot be expressed in a single chunk of code, returns an error.
    // For example, it might refer to a constant that is not in scope.
    // Takes a next_k parameter so that it can be used sequentially in the middle of
    // a bunch of code generation.
    pub fn value_to_code(&self, value: &AcornValue) -> Result<String, CodeGenError> {
        let mut var_names = vec![];
        let mut next_x = 0;
        let mut next_k = 0;
        let expr = self.value_to_expr(value, &mut var_names, &mut next_x, &mut next_k)?;
        Ok(expr.to_string())
    }

    // Given a module and a name, find an expression that refers to the name.
    // Note that:
    //   module, the canonical module of the entity we are trying to express
    // is different from
    //   self.module, the module we are trying to express the name in
    fn name_to_expr(&self, module: ModuleId, name: &str) -> Result<Expression, CodeGenError> {
        if module == self.module && self.hidden_codegen_names.contains(name) {
            return Err(CodeGenError::UnhandledValue(
                "name is declared after the selected goal".into(),
            ));
        }
        let mut parts = name.split('.').collect::<Vec<_>>();

        // Handle numeric literals
        if parts.len() == 2 && parts[1].chars().all(|ch| ch.is_ascii_digit()) {
            let numeral = TokenType::Numeral.new_token(parts[1]);

            // If it's the default type, we don't need to scope it
            if let Some((default_module, default_type_name)) = &self.default {
                if *default_module == module && default_type_name == parts[0] {
                    return Ok(Expression::Singleton(numeral));
                }
            }

            // Otherwise, we need to scope it by the type
            let numeric_type = self.name_to_expr(module, parts[0])?;
            return Ok(Expression::Binary(
                Box::new(numeric_type),
                TokenType::Dot.generate(),
                Box::new(Expression::Singleton(numeral)),
            ));
        }

        if parts.len() > 2 {
            let scope = parts[..2].join(".");
            let registered = parts.len() == 3
                && if module == self.module {
                    self.instance_scope_in_use(&scope)
                        && self.get_constant_value(&scope).is_none()
                        && self.get_constant_value(name).is_some()
                } else {
                    self.imported_instance_members
                        .contains_key(&(module, name.to_string()))
                };
            if !registered {
                return Err(CodeGenError::UnhandledValue(
                    "unregistered instance namespace".to_string(),
                ));
            }
            if module == self.module {
                return Ok(Expression::generate_identifier_chain(&parts));
            }
            let data_type = AcornType::Data(module, parts[0].to_string(), vec![]);
            if let Some(alias) = self.type_to_typename.get(&data_type) {
                return Ok(Expression::generate_identifier_chain(&[
                    alias, parts[1], parts[2],
                ]));
            }
            let module_name = self
                .module_to_name
                .get(&module)
                .ok_or_else(|| CodeGenError::UnimportedModule(module, name.to_string()))?;
            parts.insert(0, module_name);
            return Ok(Expression::generate_identifier_chain(&parts));
        }

        // Handle local constants
        if module == self.module {
            // TODO: this generates an identifier token with a dot, which is wrong
            return Ok(Expression::generate_identifier(name));
        }

        // Check if there's a local alias for this constant.
        let key = (module, name.to_string());
        if let Some(alias) = self.canonical_to_alias.get(&key) {
            return Ok(Expression::generate_identifier(alias));
        }

        // If it's a member function, check if there's a local alias for its struct.
        if parts.len() == 2 {
            if let Some(alias) = self.canonical_to_alias.get(&(module, parts[0].to_string())) {
                return Ok(Expression::generate_identifier_chain(&[alias, parts[1]]));
            }
            let data_type = AcornType::Data(module, parts[0].to_string(), vec![]);
            if let Some(type_alias) = self.type_to_typename.get(&data_type) {
                let lhs = Expression::generate_identifier(type_alias);
                let rhs = Expression::generate_identifier(parts[1]);
                return Ok(Expression::Binary(
                    Box::new(lhs),
                    TokenType::Dot.generate(),
                    Box::new(rhs),
                ));
            }
        }

        // Refer to this constant using its module
        match self.module_to_name.get(&module) {
            Some(module_name) => {
                parts.insert(0, module_name);
                Ok(Expression::generate_identifier_chain(&parts))
            }
            None => Err(CodeGenError::UnimportedModule(module, name.to_string())),
        }
    }

    // If use_x is true we use x-variables; otherwise we use k-variables.
    fn generate_quantifier_expr(
        &self,
        token_type: TokenType,
        quants: &Vec<AcornType>,
        value: &AcornValue,
        var_names: &mut Vec<String>,
        use_x: bool,
        next_x: &mut u32,
        next_k: &mut u32,
    ) -> Result<Expression, CodeGenError> {
        let initial_var_names_len = var_names.len();
        let mut decls = vec![];
        for arg_type in quants {
            let var_name = if use_x {
                self.next_x_var(next_x)
            } else {
                self.next_k_var(next_k)
            };
            let name_token = TokenType::Identifier.new_token(&var_name);
            var_names.push(var_name);
            let type_expr = self.type_to_expr(arg_type)?;
            let var_name = Declaration::Typed(name_token, type_expr);
            let decl = var_name;
            decls.push(decl);
        }
        let subresult = self.value_to_expr(value, var_names, next_x, next_k)?;
        var_names.truncate(initial_var_names_len);
        Ok(Expression::Binder(
            token_type.generate(),
            decls,
            Box::new(subresult),
            TokenType::RightBrace.generate(),
        ))
    }

    // Omit explicit arguments only when this application supplies enough typed
    // arguments to infer every formal parameter in a known declaration.
    fn can_infer_type_arguments(&self, constant: &ConstantInstance, supplied: usize) -> bool {
        let (params, signature) = if constant.module_id == self.module {
            let Some(info) = self.constant_info.get(&constant.name) else {
                return false;
            };
            let Some(signature) = self.constant_name_to_type.get(&constant.name) else {
                return false;
            };
            (&info.params, signature)
        } else {
            let Some(alias) = self
                .canonical_to_alias
                .get(&(constant.module_id, constant.name.clone()))
            else {
                return false;
            };
            let Some(PotentialValue::Unresolved(declaration)) = self.aliases.get(alias) else {
                return false;
            };
            (&declaration.params, &declaration.generic_type)
        };
        let AcornType::Function(function) = signature else {
            return false;
        };
        params.len() == constant.params.len()
            && supplied <= function.arg_types.len()
            && params.iter().all(|name| {
                function
                    .arg_types
                    .iter()
                    .take(supplied)
                    .any(|t| t.has_type_variable(&name.name))
            })
    }

    // Convert an AcornValue to an Expression.
    fn value_to_expr(
        &self,
        value: &AcornValue,
        var_names: &mut Vec<String>,
        next_x: &mut u32,
        next_k: &mut u32,
    ) -> Result<Expression, CodeGenError> {
        match value {
            AcornValue::Variable(i, _) => {
                Ok(Expression::generate_identifier(&var_names[*i as usize]))
            }
            AcornValue::Application(fa) => {
                let mut args = vec![];
                for arg in &fa.args {
                    args.push(self.value_to_expr(arg, var_names, next_x, next_k)?);
                }

                // Generic instance-style members are not supported by the evaluator.
                // Keep their class-qualified head and explicit receiver argument.
                let member = if matches!(fa.function.as_ref(), AcornValue::Constant(c) if !c.params.is_empty())
                {
                    None
                } else {
                    fa.function.is_member(&fa.args[0].get_type())
                };
                if let Some(name) = member {
                    // Keep partial or function-valued methods in member notation so
                    // subsequent application cannot change the prefix grouping.
                    if args.len() == 1 && !matches!(value.get_type(), AcornType::Function(_)) {
                        if let Some(op) = TokenType::from_magic_method_name(&name)
                            .filter(|op| op.to_prefix_magic_method_name() == Some(name.as_str()))
                        {
                            return Ok(Expression::generate_unary(op, args.pop().unwrap()));
                        }
                    }
                    if args.len() == 2 {
                        // Infix operators
                        if let Some(op) = TokenType::from_magic_method_name(&name)
                            .filter(|op| op.to_infix_magic_method_name() == Some(name.as_str()))
                        {
                            let right = args.pop().unwrap();
                            let left = args.pop().unwrap();
                            return Ok(Expression::generate_binary(left, op, right));
                        }

                        // Long numeric literals
                        if name == "read" && args[0].is_number() {
                            if let Some(digit) = args[1].to_digit() {
                                let left = args.remove(0);
                                return Ok(Expression::generate_number(left, digit));
                            }
                        }
                    }

                    // General member functions
                    let instance = args.remove(0);
                    let bound = Expression::generate_binary(
                        instance,
                        TokenType::Dot,
                        Expression::generate_identifier(&name),
                    );
                    if args.len() == 0 {
                        // Like foo.bar
                        return Ok(bound);
                    } else {
                        // Like foo.bar(baz, qux)
                        let applied = Expression::Apply(
                            Box::new(bound),
                            Box::new(Expression::generate_grouping(args)),
                        );
                        return Ok(applied);
                    }
                }

                let f = match fa.function.as_ref() {
                    AcornValue::Constant(c)
                        if !c.params.is_empty()
                            && self.can_infer_type_arguments(c, fa.args.len()) =>
                    {
                        self.name_to_expr(c.module_id, &c.name)?
                    }
                    _ => self.value_to_expr(&fa.function, var_names, next_x, next_k)?,
                };
                let grouped_args = Expression::generate_grouping(args);
                Ok(Expression::Apply(Box::new(f), Box::new(grouped_args)))
            }
            AcornValue::Binary(op, left, right) => {
                let left = self.value_to_expr(left, var_names, next_x, next_k)?;
                let right = self.value_to_expr(right, var_names, next_x, next_k)?;
                Ok(Expression::generate_binary(left, op.token_type(), right))
            }
            AcornValue::Not(x) => {
                let x = self.value_to_expr(x, var_names, next_x, next_k)?;
                Ok(Expression::generate_unary(TokenType::Not, x))
            }
            AcornValue::ForAll(quants, value) => self.generate_quantifier_expr(
                TokenType::ForAll,
                quants,
                value,
                var_names,
                true,
                next_x,
                next_k,
            ),
            AcornValue::Exists(quants, value) => self.generate_quantifier_expr(
                TokenType::Exists,
                quants,
                value,
                var_names,
                false,
                next_x,
                next_k,
            ),
            AcornValue::Lambda(quants, value) => self.generate_quantifier_expr(
                TokenType::Function,
                quants,
                value,
                var_names,
                true,
                next_x,
                next_k,
            ),
            AcornValue::Bool(b) => {
                let token = if *b {
                    TokenType::True.generate()
                } else {
                    TokenType::False.generate()
                };
                Ok(Expression::Singleton(token))
            }
            AcornValue::Constant(c) => {
                let name = self.name_to_expr(c.module_id, &c.name)?;
                if c.params.is_empty() {
                    return Ok(name);
                }
                let args = c
                    .params
                    .iter()
                    .map(|t| self.type_to_expr(t))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Expression::Apply(
                    Box::new(name),
                    Box::new(Expression::generate_type_arguments(args)),
                ))
            }
            AcornValue::IfThenElse(condition, if_value, else_value) => {
                let condition = self.value_to_expr(condition, var_names, next_x, next_k)?;
                let if_value = self.value_to_expr(if_value, var_names, next_x, next_k)?;
                let else_value = self.value_to_expr(else_value, var_names, next_x, next_k)?;
                Ok(Expression::IfThenElse(
                    TokenType::If.generate(),
                    Box::new(condition),
                    Box::new(if_value),
                    Box::new(else_value),
                    TokenType::RightBrace.generate(),
                ))
            }
            AcornValue::Match(..) => Err(CodeGenError::UnhandledValue(
                "match expression code generation is not supported yet".to_string(),
            )),
        }
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Tools for testing.
    ////////////////////////////////////////////////////////////////////////////////

    fn str_to_type(&mut self, input: &str) -> AcornType {
        let tokens = Token::scan(input);
        let mut tokens = TokenIter::new(tokens);
        let (expression, _) =
            Expression::parse_type(&mut tokens, Terminator::Is(TokenType::NewLine)).unwrap();
        match self.evaluate_type(&Project::new_mock(), &expression) {
            Ok(t) => t,
            Err(error) => panic!("Error evaluating type expression: {}", error),
        }
    }

    pub fn assert_type_ok(&mut self, input_code: &str) {
        let acorn_type = self.str_to_type(input_code);
        let type_expr = self.type_to_expr(&acorn_type).unwrap();
        let reconstructed_code = type_expr.to_string();
        let reevaluated_type = self.str_to_type(&reconstructed_code);
        assert_eq!(acorn_type, reevaluated_type);
    }

    pub fn assert_type_bad(&mut self, input: &str) {
        let tokens = Token::scan(input);
        let mut tokens = TokenIter::new(tokens);
        let expression =
            match Expression::parse_type(&mut tokens, Terminator::Is(TokenType::NewLine)) {
                Ok((expression, _)) => expression,
                Err(_) => {
                    // We expect a bad type so this is fine
                    return;
                }
            };
        assert!(self
            .evaluate_type(&Project::new_mock(), &expression)
            .is_err());
    }

    // Check that the given name actually does have this type in the environment.
    pub fn expect_type(&self, name: &str, type_string: &str) {
        let env_type = match self.constant_name_to_type.get(name) {
            Some(t) => t,
            None => panic!("{} not found", name),
        };
        assert_eq!(env_type.to_string(), type_string);
    }

    // Check that this code, when converted to a value and back to code, is the same.
    pub fn expect_good_code(&self, input_code: &str) {
        let project = Project::new_mock();
        let expression = Expression::expect_value(input_code);
        let value = self
            .evaluate_value(&project, &expression, None)
            .expect("evaluate_value failed");
        let output_code = self.value_to_code(&value).expect("value_to_code failed");
        assert_eq!(input_code, output_code);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn codegen_positions_restore_prior_aliases_module_spelling_and_numeric_default() {
        let mut bindings = BindingMap::new(FIRST_NORMAL);
        bindings.import_module("early", FIRST_NORMAL + 1);
        let item = AcornType::Data(FIRST_NORMAL + 1, "Item".into(), vec![]);
        let numeral =
            AcornValue::new_constant(FIRST_NORMAL + 1, "Item.0".into(), vec![], item.clone());
        let value =
            AcornValue::new_constant(FIRST_NORMAL + 1, "value".into(), vec![], item.clone());
        let first = bindings.codegen_position();
        bindings.add_alias(
            "first_alias",
            FIRST_NORMAL + 1,
            "value".into(),
            PotentialValue::Resolved(value.clone()),
        );
        let with_alias = bindings.codegen_position();
        bindings.import_module("later", FIRST_NORMAL + 1);
        bindings.add_type_alias("Alias", item.clone());
        bindings.add_alias(
            "second_alias",
            FIRST_NORMAL + 1,
            "value".into(),
            PotentialValue::Resolved(value.clone()),
        );
        bindings.set_default(FIRST_NORMAL + 1, "Item".into());
        bindings.add_constant("future", vec![], AcornType::Bool, None, None);
        let early = bindings.for_codegen_at(first, &ProofScope::default());
        assert_eq!(early.value_to_code(&value).unwrap(), "early.value");
        assert_eq!(early.value_to_code(&numeral).unwrap(), "early.Item.0");
        assert_eq!(
            bindings
                .for_codegen_at(with_alias, &ProofScope::default())
                .value_to_code(&value)
                .unwrap(),
            "first_alias"
        );
        assert_eq!(bindings.value_to_code(&numeral).unwrap(), "0");
        let future =
            AcornValue::new_constant(FIRST_NORMAL, "future".into(), vec![], AcornType::Bool);
        assert!(early.value_to_code(&future).is_err());
        assert!(!early.name_in_use("future"));
    }

    #[test]
    fn pattern_binding_is_transactional_and_cannot_shadow_stack_names() {
        let mut env = crate::environment::Environment::new_test();
        env.add("inductive Pair {\n pair(Bool, Bool)\n }\n");
        env.add("let pair: Pair = axiom");
        for args in [
            "first, first",
            "first, true",
            "first, outer",
            "first",
            "first, missing(value)",
        ] {
            let mut stack = Stack::new();
            stack.insert("outer".to_string(), AcornType::Bool);
            let expression =
                Expression::expect_value(&format!("match pair {{ Pair.pair({args}) {{ true }} }}"));
            assert!(
                env.bindings
                    .evaluate_value_with_stack(&mut stack, &Project::new_mock(), &expression, None)
                    .is_err(),
                "{args}"
            );
            assert_eq!(stack.names(), vec!["outer"]);
        }
        let mut stack = Stack::new();
        stack.insert("outer".to_string(), AcornType::Bool);
        let expression = Expression::expect_value(
            "match pair { Pair.pair(first, second) { first and second } }",
        );
        let value = env
            .bindings
            .evaluate_value_with_stack(&mut stack, &Project::new_mock(), &expression, None)
            .unwrap();
        assert_eq!(value.get_type(), AcornType::Bool);
        assert_eq!(stack.names(), vec!["outer"]);
    }

    #[test]
    fn match_case_body_failure_restores_outer_stack() {
        let mut env = crate::environment::Environment::new_test();
        env.add("inductive Foo {\n bar(Bool)\n }\n");
        let mut stack = Stack::new();
        stack.insert(
            "value".to_string(),
            AcornType::Data(FIRST_NORMAL, "Foo".to_string(), vec![]),
        );
        let expression = Expression::expect_value("match value { Foo.bar(local) { unknown } }");
        let error = env
            .bindings
            .evaluate_value_with_stack(&mut stack, &Project::new_mock(), &expression, None)
            .unwrap_err();
        assert!(error.to_string().contains("unknown"));
        assert_eq!(stack.names(), vec!["value"]);
    }

    #[test]
    fn repeated_constructor_cases_restore_outer_stack() {
        let mut env = crate::environment::Environment::new_test();
        env.add("inductive Foo {\n bar(Bool)\n }\n");
        let mut stack = Stack::new();
        stack.insert(
            "value".to_string(),
            AcornType::Data(FIRST_NORMAL, "Foo".to_string(), vec![]),
        );
        let expression = Expression::expect_value(
            "match value { Foo.bar(first) { first } Foo.bar(second) { second } }",
        );
        let error = env
            .bindings
            .evaluate_value_with_stack(&mut stack, &Project::new_mock(), &expression, None)
            .unwrap_err();
        assert!(error
            .to_string()
            .contains("multiple cases for the same constructor"));
        assert_eq!(stack.names(), vec!["value"]);
    }

    #[test]
    fn constructors_record_type_index_and_exhaustive_count() {
        let mut env = crate::environment::Environment::new_test();
        env.add("inductive Foo {\n bar(Bool)\n baz\n }\n");
        env.add("structure Pair {\n first: Bool\n second: Bool\n }\n");
        let foo = AcornType::Data(FIRST_NORMAL, "Foo".to_string(), vec![]);
        assert_eq!(
            env.bindings.constant_info["Foo.bar"].constructor,
            Some((foo.clone(), 0, 2))
        );
        assert_eq!(
            env.bindings.constant_info["Foo.baz"].constructor,
            Some((foo, 1, 2))
        );
        assert_eq!(
            env.bindings.constant_info["Pair.new"].constructor,
            Some((
                AcornType::Data(FIRST_NORMAL, "Pair".to_string(), vec![]),
                0,
                1
            ))
        );
        assert!(env.bindings.constant_info["Pair.first"]
            .constructor
            .is_none());
    }

    #[test]
    fn pattern_arguments_infer_constructor_parameter_types() {
        let mut env = crate::environment::Environment::new_test();
        env.add("inductive Foo {\n end\n pair(Bool, Foo)\n }\n");
        let foo = AcornType::Data(FIRST_NORMAL, "Foo".to_string(), vec![]);
        let expression = Expression::expect_value("Foo.pair(left, right)");
        let (constructor, args, index, total) = env
            .bindings
            .evaluate_pattern(&Project::new_mock(), &foo, &expression)
            .unwrap();
        assert_eq!(
            args,
            vec![
                ("left".to_string(), AcornType::Bool),
                ("right".to_string(), foo)
            ]
        );
        assert_eq!((index, total), (1, 2));
        assert_eq!(
            constructor,
            env.bindings
                .get_constant_value("Foo.pair")
                .and_then(|potential| potential.resolved())
                .unwrap()
        );
        assert!(!env.bindings.has_identifier("left"));
        assert!(!env.bindings.has_identifier("right"));
    }

    #[test]
    fn nullary_patterns_preserve_the_existing_stack() {
        let mut env = crate::environment::Environment::new_test();
        env.add("inductive Foo {\n end\n pair(Bool, Foo)\n }\n");
        let mut stack = Stack::new();
        stack.insert("outer".to_string(), AcornType::Bool);
        let expression = Expression::expect_value(
            "match Foo.end { Foo.end { outer } Foo.pair(left, right) { left } }",
        );
        env.bindings
            .evaluate_value_with_stack(&mut stack, &Project::new_mock(), &expression, None)
            .unwrap();
        assert_eq!(stack.names(), vec!["outer"]);
    }

    #[test]
    fn test_env_types() {
        let mut b = BindingMap::new(FIRST_NORMAL);
        b.assert_type_ok("Bool");
        b.assert_type_ok("Bool -> Bool");
        b.assert_type_ok("Bool -> (Bool -> Bool)");
        b.assert_type_ok("(Bool -> Bool) -> (Bool -> Bool)");
        b.assert_type_ok("(Bool, Bool) -> Bool");
        b.assert_type_bad("Bool, Bool -> Bool");
        b.assert_type_bad("(Bool, Bool)");
    }
    #[test]
    fn pattern_evaluation_validates_arguments_without_binding_them() {
        let mut env = crate::environment::Environment::new_test();
        env.add("inductive Foo {\n end\n pair(Bool, Foo)\n }\n");
        env.add("let existing: Bool = true");
        let foo = AcornType::Data(FIRST_NORMAL, "Foo".to_string(), vec![]);
        let project = Project::new_mock();
        let pattern = Expression::expect_value("Foo.pair(left, right)");
        let (constructor, args, index, total) = env
            .bindings
            .evaluate_pattern(&project, &foo, &pattern)
            .unwrap();
        assert_eq!(
            args,
            vec![
                ("left".to_string(), AcornType::Bool),
                ("right".to_string(), foo.clone())
            ]
        );
        assert_eq!((index, total), (1, 2));
        assert_eq!(
            constructor,
            env.bindings
                .get_constant_value("Foo.pair")
                .and_then(|potential| potential.resolved())
                .unwrap()
        );
        assert!(!env.bindings.has_identifier("left"));
        assert!(!env.bindings.has_identifier("right"));
        for invalid in [
            "Foo.pair",
            "Foo.pair(one)",
            "Foo.pair(same, same)",
            "Foo.pair(true, value)",
            "Foo.pair(existing, value)",
        ] {
            let pattern = Expression::expect_value(invalid);
            assert!(
                env.bindings
                    .evaluate_pattern(&project, &foo, &pattern)
                    .is_err(),
                "{invalid}"
            );
        }
    }
}
