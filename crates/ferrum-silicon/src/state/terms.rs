// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

//! Symbolic term foundations from
//! <https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/state/Terms.scala>.
//!
//! Status: sorts, identity, variables, applications, literals, arithmetic, boolean,
//! comparisons, permissions, collections and selected snapshot/heap constructors are
//! implemented, along with declarations and partial quantifier/traversal support.
//! Resource-keyed nodes and dispatch are implemented; chunk-backed wand terms,
//! parts of traversal and display remain incomplete.

use std::fmt;

use super::chunks::MagicWandIdentifier;
use super::identifiers::Identifier;
use crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet;
use ferrum_silver::ast::program::{Field, Predicate};

/// Distinct source sort cases. Field and predicate names do not encode codomain identity.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Sort {
    Snap,
    Int,
    Bool,
    Ref,
    Perm,
    Unit,
    Seq(Box<Sort>),
    Set(Box<Sort>),
    Multiset(Box<Sort>),
    Map(Box<Sort>, Box<Sort>),
    UserSort(Identifier),
    SmtSort(Identifier),
    FieldValueFunction {
        codomain: Box<Sort>,
        field_name: String,
    },
    PredicateSnapFunction {
        codomain: Box<Sort>,
        predicate_name: String,
    },
    MagicWandSnapFunction,
    FieldPermFunction,
    PredicatePermFunction,
    Heap(Box<Sort>),
    WandHeap,
    PredHeap,
    PredMask,
}

impl Sort {
    pub fn mask() -> Self {
        Self::Heap(Box::new(Self::Perm))
    }

    pub fn id(&self) -> Identifier {
        match self {
            Self::UserSort(id) | Self::SmtSort(id) => id.clone(),
            _ => Identifier::new(self.to_string()),
        }
    }
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Snap => f.write_str("Snap"),
            Self::Int => f.write_str("Int"),
            Self::Bool => f.write_str("Bool"),
            Self::Ref => f.write_str("Ref"),
            Self::Perm => f.write_str("Perm"),
            Self::Unit => f.write_str("()"),
            Self::Seq(s) => write!(f, "Seq[{s}]"),
            Self::Set(s) => write!(f, "Set[{s}]"),
            Self::Multiset(s) => write!(f, "Multiset[{s}]"),
            Self::Map(k, v) => write!(f, "Map[{k},{v}]"),
            Self::UserSort(id) | Self::SmtSort(id) => write!(f, "{id}"),
            Self::FieldValueFunction { field_name, .. } => write!(f, "FVF[{field_name}]"),
            Self::PredicateSnapFunction { predicate_name, .. } => {
                write!(f, "PSF[{predicate_name}]")
            }
            Self::MagicWandSnapFunction => f.write_str("MWSF"),
            Self::FieldPermFunction => f.write_str("FPM"),
            Self::PredicatePermFunction => f.write_str("PPM"),
            Self::Heap(value) => write!(f, "Hp[{value}]"),
            Self::WandHeap => f.write_str("Hp[MWSF]"),
            Self::PredHeap => f.write_str("Hp[Pred]"),
            Self::PredMask => f.write_str("Hp[PredMask]"),
        }
    }
}

use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::sync::atomic::{AtomicI32, Ordering};
use std::sync::{Arc, Mutex, OnceLock};

use ferrum_silver::utility::common::Rational;
use num_bigint::BigInt;

/// A symbolic variable. Wildcards remain distinct from ordinary variables.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Var {
    pub id: Identifier,
    pub sort: Sort,
    pub is_wildcard: bool,
}

/// Typed cases implemented so far; other source cases are still being ported.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TermKind {
    Unit,
    IntLiteral(BigInt),
    Null,
    ZeroMask,
    PredZeroMask,
    True,
    False,
    Var(Var),
    App {
        applicable: ApplicationTarget,
        args: Vec<Term>,
    },
    AppHint(ApplicationTarget),
    Distinct(DomainFunctions),
    Let(Bindings, Term),
    Quantification {
        quantifier: Quantifier,
        vars: Vec<Term>,
        body: Term,
        triggers: Vec<Trigger>,
        name: String,
        is_global: bool,
        weight: Option<i32>,
    },
    Plus(Term, Term),
    Minus(Term, Term),
    Times(Term, Term),
    Div(Term, Term),
    Mod(Term, Term),
    Not(Term),
    Or(Vec<Term>),
    And(Vec<Term>),
    Implies(Term, Term),
    Iff(Term, Term),
    Ite(Term, Term, Term),
    BuiltinEquals(Term, Term),
    CustomEquals(Term, Term),
    Less(Term, Term),
    AtMost(Term, Term),
    Greater(Term, Term),
    AtLeast(Term, Term),
    NoPerm,
    FullPerm,
    FractionPermLiteral(Rational),
    FractionPerm(Term, Term),
    IsValidPermVal(Term),
    IsReadPermVar(Term),
    PermTimes(Term, Term),
    IntPermTimes(Term, Term),
    PermIntDiv(Term, Term),
    PermPermDiv(Term, Term),
    PermPlus(Term, Term),
    PermMinus(Term, Term),
    PermNegation(Term),
    PermLess(Term, Term),
    PermAtMost(Term, Term),
    PermMin(Term, Term),
    SeqRanged(Term, Term),
    SeqNil(Sort),
    SeqSingleton(Term),
    SeqAppend(Term, Term),
    SeqDrop(Term, Term),
    SeqTake(Term, Term),
    SeqLength(Term),
    SeqAt(Term, Term),
    SeqIn(Term, Term),
    SeqInTrigger(Term, Term),
    SeqUpdate(Term, Term, Term),
    EmptySet(Sort),
    SingletonSet(Term),
    SetAdd(Term, Term),
    SetUnion(Term, Term),
    SetIntersection(Term, Term),
    SetSubset(Term, Term),
    SetDisjoint(Term, Term),
    SetDifference(Term, Term),
    SetIn(Term, Term),
    SetCardinality(Term),
    EmptyMultiset(Sort),
    SingletonMultiset(Term),
    MultisetAdd(Term, Term),
    MultisetUnion(Term, Term),
    MultisetIntersection(Term, Term),
    MultisetSubset(Term, Term),
    MultisetDifference(Term, Term),
    MultisetCardinality(Term),
    MultisetCount(Term, Term),
    EmptyMap(Sort, Sort),
    MapLookup(Term, Term),
    MapCardinality(Term),
    MapUpdate(Term, Term, Term),
    MapDomain(Term),
    MapRange(Term),
    SortWrapper(Term, Sort),
    Combine(Term, Term),
    First(Term),
    Second(Term),
    MagicWandSnapshot(Term),
    MwsfLookup(Term, Term),
    MagicWandToken(Term, Term),
    Lookup(String, Term, Term),
    PermLookup(String, Term, Term),
    Domain(String, Term),
    HasDomain(String, Term, bool),
    FieldTrigger(String, Term, Term),
    PredicateLookup(String, Term, Vec<Term>),
    PredicatePermLookup(String, Term, Vec<Term>),
    PredicateDomain(String, Term),
    HasPredicateDomain(String, Term, bool),
    PredicateTrigger(String, Term, Vec<Term>),
    HeapToSnap(Term, Term, ResourceKey),
    SnapToHeap(Term, ResourceKey, Sort),
    MaskMapTerm(ResourceMap),
    HeapMapTerm(ResourceMap),
    HeapLookup(Term, Term),
    HeapUpdate(Term, Term, Term),
    MaskAdd(Term, Term, Term),
    HeapSingleton(Term, Term, Sort),
    IdenticalOnKnownLocations(Term, Term, Term),
    GoodMask(Term),
    GoodFieldMask(Term, bool),
    MergeSingle(Term, Term, Term, Term),
    MergeHeaps(Term, Term, Term, Term),
    HeapsOverlap(Term, Term, Term, Term),
    MaskEq(Term, Term),
    MaskSum(Term, Term),
    MaskDiff(Term, Term),
    DummyHeap(Sort),
}

/// The four function classes and Macro have independent upstream flyweight pools.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ApplicableKind {
    Fun,
    HeapDepFun,
    DomainFun,
    SmtFun,
    Macro,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ApplicableData {
    pub kind: ApplicableKind,
    pub id: Identifier,
    pub arg_sorts: Vec<Sort>,
    pub result_sort: Sort,
}

#[derive(Debug)]
struct ApplicableNode {
    data: ApplicableData,
    flyweight: bool,
}

#[derive(Clone, Debug)]
pub struct Applicable(Arc<ApplicableNode>);
impl Applicable {
    pub fn data(&self) -> &ApplicableData {
        &self.0.data
    }
    pub fn ptr_eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
    pub fn uses_flyweight(&self) -> bool {
        self.0.flyweight
    }
}
impl PartialEq for Applicable {
    fn eq(&self, other: &Self) -> bool {
        if self.0.flyweight != other.0.flyweight {
            return false;
        }
        if self.0.flyweight {
            self.ptr_eq(other)
        } else {
            self.0.data == other.0.data
        }
    }
}
impl Eq for Applicable {}
impl Hash for Applicable {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.flyweight.hash(state);
        if self.0.flyweight {
            Arc::as_ptr(&self.0).hash(state);
        } else {
            self.0.data.hash(state);
        }
    }
}
static APPLICABLE_POOL: OnceLock<Mutex<HashMap<ApplicableData, Arc<ApplicableNode>>>> =
    OnceLock::new();

/// Upstream declaration classes; constant declarations are function declarations of variables.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum DeclarationKind {
    Sort(Sort),
    Function(ApplicationTarget),
    SortWrapper(Sort, Sort),
    Macro {
        id: Identifier,
        args: Vec<Term>,
        body: Term,
    },
}
#[derive(Debug)]
struct DeclarationNode {
    kind: DeclarationKind,
    flyweight: bool,
}
#[derive(Clone, Debug)]
pub struct Declaration(Arc<DeclarationNode>);
impl Declaration {
    pub fn kind(&self) -> &DeclarationKind {
        &self.0.kind
    }
    pub fn ptr_eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
    pub fn id(&self) -> Identifier {
        match self.kind() {
            DeclarationKind::Sort(sort) => sort.id(),
            DeclarationKind::Function(fun) => fun.id().clone(),
            DeclarationKind::SortWrapper(from, to) => sort_wrapper_id(from.clone(), to.clone()),
            DeclarationKind::Macro { id, .. } => id.clone(),
        }
    }
}
impl PartialEq for Declaration {
    fn eq(&self, other: &Self) -> bool {
        if self.0.flyweight != other.0.flyweight {
            return false;
        }
        if self.0.flyweight {
            self.ptr_eq(other)
        } else {
            self.0.kind == other.0.kind
        }
    }
}
impl Eq for Declaration {}
impl Hash for Declaration {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.flyweight.hash(state);
        if self.0.flyweight {
            Arc::as_ptr(&self.0).hash(state);
        } else {
            self.0.kind.hash(state);
        }
    }
}
static DECLARATION_POOL: OnceLock<Mutex<HashMap<DeclarationKind, Arc<DeclarationNode>>>> =
    OnceLock::new();

pub fn sort_wrapper_id(from: Sort, to: Sort) -> Identifier {
    Identifier::sort_based("$SortWrappers.%sTo%s", vec![from, to])
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Quantifier {
    Forall,
    Exists,
}
/// Triggers are structural rather than flyweights, as in Triggers.scala.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Trigger {
    pub terms: Vec<Term>,
}

/// Variables, functions and macros can all be application targets upstream.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ApplicationTarget {
    Function(Applicable),
    Variable(Term),
}
impl ApplicationTarget {
    pub fn id(&self) -> &Identifier {
        match self {
            Self::Function(f) => &f.data().id,
            Self::Variable(v) => match v.kind() {
                TermKind::Var(var) => &var.id,
                _ => unreachable!("validated variable target"),
            },
        }
    }
    pub fn result_sort(&self) -> &Sort {
        match self {
            Self::Function(f) => &f.data().result_sort,
            Self::Variable(v) => v.sort(),
        }
    }
}

/// Order-preserving entries with map equality; order is not equality-defining upstream.
#[derive(Clone, Debug)]
pub struct Bindings(Vec<(Term, Term)>);
impl Bindings {
    pub fn iter(&self) -> impl Iterator<Item = &(Term, Term)> {
        self.0.iter()
    }
}
impl PartialEq for Bindings {
    fn eq(&self, other: &Self) -> bool {
        self.0.len() == other.0.len()
            && self
                .0
                .iter()
                .all(|(k, v)| other.0.iter().any(|(k2, v2)| k == k2 && v == v2))
    }
}
impl Eq for Bindings {}
impl Hash for Bindings {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut combined = 0u64;
        for entry in &self.0 {
            let mut h = std::collections::hash_map::DefaultHasher::new();
            entry.hash(&mut h);
            combined = combined.wrapping_add(h.finish());
        }
        self.0.len().hash(state);
        combined.hash(state);
    }
}
#[derive(Clone, Debug)]
pub struct DomainFunctions(Vec<Applicable>);
impl DomainFunctions {
    pub fn iter(&self) -> impl Iterator<Item = &Applicable> {
        self.0.iter()
    }
}
impl PartialEq for DomainFunctions {
    fn eq(&self, other: &Self) -> bool {
        self.0.len() == other.0.len() && self.0.iter().all(|f| other.0.contains(f))
    }
}
impl Eq for DomainFunctions {}
impl Hash for DomainFunctions {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut combined = 0u64;
        for entry in &self.0 {
            let mut h = std::collections::hash_map::DefaultHasher::new();
            entry.hash(&mut h);
            combined = combined.wrapping_add(h.finish());
        }
        self.0.len().hash(state);
        combined.hash(state);
    }
}

/// Concrete program resources; structural equality is delegated to Silver and wand
/// equality uses its structure index. Member-name hashes are a valid (coarse) subset
/// of Silver equality until its full structural Hash implementations are available.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResourceKey {
    Field(Arc<Field>),
    Predicate(Arc<Predicate>),
    Wand(MagicWandIdentifier),
}
impl Hash for ResourceKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Self::Field(f) => {
                0u8.hash(state);
                f.name.hash(state);
            }
            Self::Predicate(p) => {
                1u8.hash(state);
                p.name.hash(state);
            }
            Self::Wand(w) => {
                2u8.hash(state);
                w.hash(state);
            }
        }
    }
}
/// A resource map preserves insertion order while comparing as a Scala map.
#[derive(Clone, Debug)]
pub struct ResourceMap(Vec<(ResourceKey, Term)>);
impl ResourceMap {
    pub fn iter(&self) -> impl Iterator<Item = &(ResourceKey, Term)> {
        self.0.iter()
    }
}
impl PartialEq for ResourceMap {
    fn eq(&self, other: &Self) -> bool {
        self.0.len() == other.0.len()
            && self
                .0
                .iter()
                .all(|(k, v)| other.0.iter().any(|(k2, v2)| k == k2 && v == v2))
    }
}
impl Eq for ResourceMap {}
impl Hash for ResourceMap {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut combined = 0u64;
        for entry in &self.0 {
            let mut h = std::collections::hash_map::DefaultHasher::new();
            entry.hash(&mut h);
            combined = combined.wrapping_add(h.finish());
        }
        self.0.len().hash(state);
        combined.hash(state);
    }
}

#[derive(Debug)]
struct TermNode {
    kind: TermKind,
    sort: Sort,
    flyweight: bool,
    var_repr: Mutex<Option<Term>>,
}

/// An immutable symbolic node. Equality mode is pinned for its lifetime.
/// Terms built in different modes compare unequal; a factory rejects mixed-mode inputs.
#[derive(Clone, Debug)]
pub struct Term(Arc<TermNode>);

impl Term {
    pub fn kind(&self) -> &TermKind {
        &self.0.kind
    }
    pub fn sort(&self) -> &Sort {
        &self.0.sort
    }
    pub fn ptr_eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
    pub fn uses_flyweight(&self) -> bool {
        self.0.flyweight
    }
    fn has_var_repr(&self) -> bool {
        matches!(
            self.kind(),
            TermKind::HeapUpdate(..)
                | TermKind::HeapToSnap(..)
                | TermKind::SnapToHeap(..)
                | TermKind::MaskAdd(..)
                | TermKind::MergeSingle(..)
                | TermKind::MergeHeaps(..)
        )
    }
    /// Mutable auxiliary representation is excluded from identity and structural equality.
    pub fn var_repr(&self) -> Option<Term> {
        assert!(
            self.has_var_repr(),
            "term has no auxiliary variable representation"
        );
        self.0
            .var_repr
            .lock()
            .expect("variable representation lock poisoned")
            .clone()
    }
    pub fn set_var_repr(&self, repr: Option<Term>) {
        assert!(
            self.has_var_repr(),
            "term has no auxiliary variable representation"
        );
        if let Some(ref term) = repr {
            assert!(
                matches!(term.kind(), TermKind::App { .. }),
                "representation must be an application"
            );
            assert_eq!(
                term.uses_flyweight(),
                self.uses_flyweight(),
                "cannot mix flyweight modes"
            );
        }
        *self
            .0
            .var_repr
            .lock()
            .expect("variable representation lock poisoned") = repr;
    }
}

impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        if self.0.flyweight != other.0.flyweight {
            return false;
        }
        if self.0.flyweight && !matches!(self.kind(), TermKind::AppHint(_)) {
            self.ptr_eq(other)
        } else {
            self.0.kind == other.0.kind
        }
    }
}
impl Eq for Term {}
impl Hash for Term {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.flyweight.hash(state);
        if self.0.flyweight && !matches!(self.kind(), TermKind::AppHint(_)) {
            Arc::as_ptr(&self.0).hash(state);
        } else {
            self.0.kind.hash(state);
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TermOptions {
    pub use_flyweight: bool,
    pub use_old_axiomatization: bool,
    pub mask_heap_mode: bool,
}

/// Factory options are explicit. All terms used in one graph must share the same
/// flyweight mode; this replaces upstream's mutable global equality configuration.
#[derive(Clone, Debug)]
pub struct TermFactory {
    options: TermOptions,
}

static TERM_POOL: OnceLock<Mutex<HashMap<TermKind, Arc<TermNode>>>> = OnceLock::new();
// Scala case objects retain singleton identity independently of flyweight configuration.
// Keep a separate singleton per Rust equality mode, since mixed modes are rejected.
static CONSTANT_POOL: OnceLock<Mutex<HashMap<(TermKind, bool), Arc<TermNode>>>> = OnceLock::new();

impl TermFactory {
    pub fn new(options: TermOptions) -> Self {
        Self { options }
    }
    pub fn options(&self) -> TermOptions {
        self.options
    }

    fn check(&self, terms: &[&Term]) {
        assert!(
            terms
                .iter()
                .all(|t| t.uses_flyweight() == self.options.use_flyweight),
            "cannot mix term flyweight modes in one factory graph"
        );
    }

    fn create(&self, kind: TermKind, sort: Sort) -> Term {
        if matches!(
            kind,
            TermKind::Unit
                | TermKind::Null
                | TermKind::ZeroMask
                | TermKind::PredZeroMask
                | TermKind::True
                | TermKind::False
                | TermKind::NoPerm
                | TermKind::FullPerm
        ) {
            let key = (kind.clone(), self.options.use_flyweight);
            let mut pool = CONSTANT_POOL
                .get_or_init(|| Mutex::new(HashMap::new()))
                .lock()
                .expect("constant pool poisoned");
            return Term(
                pool.entry(key)
                    .or_insert_with(|| {
                        Arc::new(TermNode {
                            kind,
                            sort,
                            flyweight: self.options.use_flyweight,
                            var_repr: Mutex::new(None),
                        })
                    })
                    .clone(),
            );
        }
        if !self.options.use_flyweight || matches!(kind, TermKind::AppHint(_)) {
            return Term(Arc::new(TermNode {
                kind,
                sort,
                flyweight: self.options.use_flyweight,
                var_repr: Mutex::new(None),
            }));
        }
        let mut pool = TERM_POOL
            .get_or_init(|| Mutex::new(HashMap::new()))
            .lock()
            .expect("term flyweight pool poisoned");
        Term(
            pool.entry(kind.clone())
                .or_insert_with(|| {
                    Arc::new(TermNode {
                        kind,
                        sort,
                        flyweight: true,
                        var_repr: Mutex::new(None),
                    })
                })
                .clone(),
        )
    }

    pub fn unit(&self) -> Term {
        self.create(TermKind::Unit, Sort::Snap)
    }
    pub fn int_literal(&self, value: impl Into<BigInt>) -> Term {
        self.create(TermKind::IntLiteral(value.into()), Sort::Int)
    }
    pub fn null(&self) -> Term {
        self.create(TermKind::Null, Sort::Ref)
    }
    pub fn zero_mask(&self) -> Term {
        self.create(TermKind::ZeroMask, Sort::mask())
    }
    pub fn pred_zero_mask(&self) -> Term {
        self.create(TermKind::PredZeroMask, Sort::PredMask)
    }
    pub fn boolean(&self, value: bool) -> Term {
        self.create(
            if value {
                TermKind::True
            } else {
                TermKind::False
            },
            Sort::Bool,
        )
    }
    pub fn var(&self, id: Identifier, sort: Sort, is_wildcard: bool) -> Term {
        self.create(
            TermKind::Var(Var {
                id,
                sort: sort.clone(),
                is_wildcard,
            }),
            sort,
        )
    }

    pub fn plus(&self, left: Term, right: Term) -> Term {
        self.check(&[&left, &right]);
        match (left.kind(), right.kind()) {
            (_, TermKind::IntLiteral(n)) if n == &BigInt::from(0) => left,
            (TermKind::IntLiteral(n), _) if n == &BigInt::from(0) => right,
            (TermKind::IntLiteral(a), TermKind::IntLiteral(b)) => self.int_literal(a + b),
            _ => self.create(TermKind::Plus(left, right), Sort::Int),
        }
    }
    pub fn minus(&self, left: Term, right: Term) -> Term {
        self.check(&[&left, &right]);
        match (left.kind(), right.kind()) {
            (_, TermKind::IntLiteral(n)) if n == &BigInt::from(0) => left,
            (TermKind::IntLiteral(a), TermKind::IntLiteral(b)) => self.int_literal(a - b),
            _ if left == right => self.int_literal(0),
            _ => self.create(TermKind::Minus(left, right), Sort::Int),
        }
    }
    pub fn times(&self, left: Term, right: Term) -> Term {
        self.check(&[&left, &right]);
        match (left.kind(), right.kind()) {
            (_, TermKind::IntLiteral(n)) | (TermKind::IntLiteral(n), _)
                if n == &BigInt::from(0) =>
            {
                self.int_literal(0)
            }
            (_, TermKind::IntLiteral(n)) if n == &BigInt::from(1) => left,
            (TermKind::IntLiteral(n), _) if n == &BigInt::from(1) => right,
            (TermKind::IntLiteral(a), TermKind::IntLiteral(b)) => self.int_literal(a * b),
            _ => self.create(TermKind::Times(left, right), Sort::Int),
        }
    }
    pub fn div(&self, left: Term, right: Term) -> Term {
        self.check(&[&left, &right]);
        self.create(TermKind::Div(left, right), Sort::Int)
    }
    pub fn modulo(&self, left: Term, right: Term) -> Term {
        self.check(&[&left, &right]);
        self.create(TermKind::Mod(left, right), Sort::Int)
    }
}

impl TermFactory {
    pub fn not(&self, term: Term) -> Term {
        self.check(&[&term]);
        match term.kind() {
            TermKind::Not(inner) => inner.clone(),
            TermKind::True => self.boolean(false),
            TermKind::False => self.boolean(true),
            _ => {
                assert_eq!(term.sort(), &Sort::Bool);
                self.create(TermKind::Not(term), Sort::Bool)
            }
        }
    }

    pub fn and(&self, terms: impl IntoIterator<Item = Term>) -> Term {
        self.junction(terms.into_iter().collect(), true)
    }
    pub fn or(&self, terms: impl IntoIterator<Item = Term>) -> Term {
        self.junction(terms.into_iter().collect(), false)
    }
    fn junction(&self, terms: Vec<Term>, and: bool) -> Term {
        self.check(&terms.iter().collect::<Vec<_>>());
        // Upstream computes a flattened sequence, then overwrites it using the
        // original input; preserve that observable nesting and distinct order.
        let mut filtered = Vec::new();
        for term in terms {
            if matches!(
                (and, term.kind()),
                (true, TermKind::True) | (false, TermKind::False)
            ) {
                continue;
            }
            if !filtered.contains(&term) {
                filtered.push(term);
            }
        }
        if filtered.is_empty() {
            return self.boolean(and);
        }
        if filtered.len() == 1 {
            return filtered.pop().unwrap();
        }
        if filtered.iter().any(|t| {
            matches!(
                (and, t.kind()),
                (true, TermKind::False) | (false, TermKind::True)
            )
        }) {
            return self.boolean(!and);
        }
        self.create(
            if and {
                TermKind::And(filtered)
            } else {
                TermKind::Or(filtered)
            },
            Sort::Bool,
        )
    }
    pub fn implies(&self, left: Term, right: Term) -> Term {
        self.check(&[&left, &right]);
        match (left.kind(), right.kind()) {
            (TermKind::True, _) => right,
            (TermKind::False, _) | (_, TermKind::True) => self.boolean(true),
            (_, TermKind::Implies(a, b)) => {
                self.implies(self.and([left.clone(), a.clone()]), b.clone())
            }
            _ if left == right => self.boolean(true),
            _ => self.create(TermKind::Implies(left, right), Sort::Bool),
        }
    }
    pub fn iff(&self, left: Term, right: Term) -> Term {
        self.check(&[&left, &right]);
        match (left.kind(), right.kind()) {
            (TermKind::True, _) => right,
            (_, TermKind::True) => left,
            _ if left == right => self.boolean(true),
            _ => self.create(TermKind::Iff(left, right), Sort::Bool),
        }
    }
    pub fn ite(&self, condition: Term, yes: Term, no: Term) -> Term {
        self.check(&[&condition, &yes, &no]);
        if yes == no {
            return yes;
        }
        match (condition.kind(), yes.kind(), no.kind()) {
            (TermKind::True, _, _) => yes,
            (TermKind::False, _, _) => no,
            (_, TermKind::True, TermKind::False) => condition,
            (_, TermKind::False, TermKind::True) => self.not(condition),
            _ => {
                assert_eq!(condition.sort(), &Sort::Bool);
                assert_eq!(yes.sort(), no.sort());
                let sort = yes.sort().clone();
                self.create(TermKind::Ite(condition, yes, no), sort)
            }
        }
    }
    pub fn equals(&self, left: Term, right: Term) -> Term {
        self.check(&[&left, &right]);
        assert_eq!(left.sort(), right.sort());
        if left == right {
            return self.boolean(true);
        }
        if let (Some(a), Some(b)) = (
            Self::permission_literal(&left),
            Self::permission_literal(&right),
        ) {
            return self.boolean(a == b);
        }
        if Self::is_literal(&left) && Self::is_literal(&right) {
            return self.boolean(false);
        }
        if let (TermKind::SortWrapper(a, _), TermKind::SortWrapper(b, _)) =
            (left.kind(), right.kind())
        {
            if left.sort() == &Sort::Snap {
                assert_eq!(
                    a.sort(),
                    b.sort(),
                    "equality between differently wrapped snapshots"
                );
            }
        }
        let custom = matches!(
            left.sort(),
            Sort::Seq(_) | Sort::Set(_) | Sort::Multiset(_) | Sort::Map(_, _)
        );
        self.create(
            if custom {
                TermKind::CustomEquals(left, right)
            } else {
                TermKind::BuiltinEquals(left, right)
            },
            Sort::Bool,
        )
    }
    fn is_literal(t: &Term) -> bool {
        matches!(
            t.kind(),
            TermKind::Unit
                | TermKind::IntLiteral(_)
                | TermKind::Null
                | TermKind::ZeroMask
                | TermKind::PredZeroMask
                | TermKind::True
                | TermKind::False
                | TermKind::SeqNil(_)
                | TermKind::EmptySet(_)
                | TermKind::EmptyMultiset(_)
                | TermKind::EmptyMap(_, _)
        )
    }
}

impl TermFactory {
    pub fn applicable(&self, data: ApplicableData) -> Applicable {
        if !self.options.use_flyweight {
            return Applicable(Arc::new(ApplicableNode {
                data,
                flyweight: false,
            }));
        }
        let mut pool = APPLICABLE_POOL
            .get_or_init(|| Mutex::new(HashMap::new()))
            .lock()
            .expect("applicable flyweight pool poisoned");
        Applicable(
            pool.entry(data.clone())
                .or_insert_with(|| {
                    Arc::new(ApplicableNode {
                        data,
                        flyweight: true,
                    })
                })
                .clone(),
        )
    }
    pub fn app(&self, applicable: Applicable, args: Vec<Term>) -> Term {
        assert_eq!(
            applicable.uses_flyweight(),
            self.options.use_flyweight,
            "cannot mix flyweight modes"
        );
        self.check(&args.iter().collect::<Vec<_>>());
        assert_eq!(
            applicable.data().arg_sorts.len(),
            args.len(),
            "wrong number of arguments"
        );
        for (expected, arg) in applicable.data().arg_sorts.iter().zip(&args) {
            assert_eq!(expected, arg.sort(), "application argument sort mismatch");
        }
        let sort = applicable.data().result_sort.clone();
        self.create(
            TermKind::App {
                applicable: ApplicationTarget::Function(applicable),
                args,
            },
            sort,
        )
    }
}

impl TermFactory {
    fn permission_literal(t: &Term) -> Option<Rational> {
        match t.kind() {
            TermKind::NoPerm => Some(Rational::zero()),
            TermKind::FullPerm => Some(Rational::one()),
            TermKind::FractionPermLiteral(value) => Some(value.clone()),
            _ => None,
        }
    }
    pub fn no_perm(&self) -> Term {
        self.create(TermKind::NoPerm, Sort::Perm)
    }
    pub fn full_perm(&self) -> Term {
        self.create(TermKind::FullPerm, Sort::Perm)
    }
    pub fn fraction_perm_literal(&self, value: Rational) -> Term {
        if value == Rational::zero() {
            self.no_perm()
        } else if value == Rational::one() {
            self.full_perm()
        } else {
            self.create(TermKind::FractionPermLiteral(value), Sort::Perm)
        }
    }
    pub fn fraction_perm(&self, numerator: Term, denominator: Term) -> Term {
        self.check(&[&numerator, &denominator]);
        if let (TermKind::IntLiteral(n), TermKind::IntLiteral(d)) =
            (numerator.kind(), denominator.kind())
        {
            if d != &BigInt::from(0) {
                return self.fraction_perm_literal(Rational::new(n.clone(), d.clone()));
            }
        }
        self.create(TermKind::FractionPerm(numerator, denominator), Sort::Perm)
    }
    pub fn is_valid_perm_val(&self, term: Term) -> Term {
        self.check(&[&term]);
        self.create(TermKind::IsValidPermVal(term), Sort::Bool)
    }
    pub fn is_read_perm_var(&self, var: Term) -> Term {
        self.check(&[&var]);
        assert!(
            matches!(var.kind(), TermKind::Var(_)),
            "expected a variable"
        );
        self.create(TermKind::IsReadPermVar(var), Sort::Bool)
    }
}

impl TermFactory {
    pub fn perm_times(&self, a: Term, b: Term) -> Term {
        self.check(&[&a, &b]);
        match (a.kind(), b.kind()) {
            (TermKind::FullPerm, _) => return b,
            (_, TermKind::FullPerm) => return a,
            (TermKind::NoPerm, _) | (_, TermKind::NoPerm) => return self.no_perm(),
            _ => {}
        }
        if let (Some(x), Some(y)) = (Self::permission_literal(&a), Self::permission_literal(&b)) {
            return self.fraction_perm_literal(x * y);
        }
        match (a.kind(), b.kind()) {
            (TermKind::Ite(c, x, y), _) => self.ite(
                c.clone(),
                self.perm_times(x.clone(), b.clone()),
                self.perm_times(y.clone(), b.clone()),
            ),
            (TermKind::PermPlus(x, y), _) => self.perm_plus(
                self.perm_times(x.clone(), b.clone()),
                self.perm_times(y.clone(), b.clone()),
            ),
            (_, TermKind::PermPlus(x, y)) => self.perm_plus(
                self.perm_times(a.clone(), x.clone()),
                self.perm_times(a.clone(), y.clone()),
            ),
            (TermKind::PermMinus(x, y), _) => self.perm_minus(
                self.perm_times(x.clone(), b.clone()),
                self.perm_times(y.clone(), b.clone()),
            ),
            (_, TermKind::PermMinus(x, y)) => self.perm_minus(
                self.perm_times(a.clone(), x.clone()),
                self.perm_times(a.clone(), y.clone()),
            ),
            (_, TermKind::Ite(c, x, y)) => self.ite(
                c.clone(),
                self.perm_times(a.clone(), x.clone()),
                self.perm_times(a.clone(), y.clone()),
            ),
            _ => self.create(TermKind::PermTimes(a, b), Sort::Perm),
        }
    }
    pub fn wildcard_simplifying_perm_times(&self, a: Term, b: Term) -> Term {
        self.check(&[&a, &b]);
        match (a.kind(), b.kind()) {
            (TermKind::Var(x), TermKind::Var(y)) if x.is_wildcard && y.is_wildcard => {
                return if x
                    .id
                    .name()
                    .encode_utf16()
                    .cmp(y.id.name().encode_utf16())
                    .is_gt()
                {
                    a
                } else {
                    b
                };
            }
            (TermKind::Var(x), _)
                if x.is_wildcard
                    && Self::permission_literal(&b).is_some_and(|p| p > Rational::zero()) =>
            {
                return a;
            }
            (_, TermKind::Var(y))
                if y.is_wildcard
                    && Self::permission_literal(&a).is_some_and(|p| p > Rational::zero()) =>
            {
                return b;
            }
            (TermKind::Ite(c, x, y), _) => {
                return self.ite(
                    c.clone(),
                    self.wildcard_simplifying_perm_times(x.clone(), b.clone()),
                    self.wildcard_simplifying_perm_times(y.clone(), b.clone()),
                );
            }
            (TermKind::PermPlus(x, y), _) => {
                return self.perm_plus(
                    self.wildcard_simplifying_perm_times(x.clone(), b.clone()),
                    self.wildcard_simplifying_perm_times(y.clone(), b.clone()),
                );
            }
            (_, TermKind::PermPlus(x, y)) => {
                return self.perm_plus(
                    self.wildcard_simplifying_perm_times(a.clone(), x.clone()),
                    self.wildcard_simplifying_perm_times(a.clone(), y.clone()),
                );
            }
            (TermKind::PermMinus(x, y), _) => {
                return self.perm_minus(
                    self.wildcard_simplifying_perm_times(x.clone(), b.clone()),
                    self.wildcard_simplifying_perm_times(y.clone(), b.clone()),
                );
            }
            (_, TermKind::PermMinus(x, y)) => {
                return self.perm_minus(
                    self.wildcard_simplifying_perm_times(a.clone(), x.clone()),
                    self.wildcard_simplifying_perm_times(a.clone(), y.clone()),
                );
            }
            (_, TermKind::Ite(c, x, y)) => {
                return self.ite(
                    c.clone(),
                    self.wildcard_simplifying_perm_times(a.clone(), x.clone()),
                    self.wildcard_simplifying_perm_times(a.clone(), y.clone()),
                );
            }
            _ => {}
        }
        self.perm_times(a, b)
    }
    pub fn int_perm_times(&self, a: Term, b: Term) -> Term {
        self.check(&[&a, &b]);
        match (a.kind(), b.kind()) {
            (TermKind::IntLiteral(i), _) if i == &BigInt::from(0) => return self.no_perm(),
            (TermKind::IntLiteral(i), _) if i == &BigInt::from(1) => return b,
            (_, TermKind::NoPerm) => return self.no_perm(),
            (TermKind::IntLiteral(i), _) => {
                if let Some(p) = Self::permission_literal(&b) {
                    return self.fraction_perm_literal(Rational::new(i.clone(), 1.into()) * p);
                }
            }
            _ => {}
        }
        self.create(TermKind::IntPermTimes(a, b), Sort::Perm)
    }
    pub fn perm_int_div(&self, a: Term, b: Term) -> Term {
        self.check(&[&a, &b]);
        if let TermKind::IntLiteral(i) = b.kind() {
            if i == &BigInt::from(1) {
                return a;
            }
            if i != &BigInt::from(0) {
                if let Some(p) = Self::permission_literal(&a) {
                    return self.fraction_perm_literal(p / Rational::new(i.clone(), 1.into()));
                }
            }
        }
        assert_eq!(b.sort(), &Sort::Int);
        self.create(TermKind::PermIntDiv(a, b), Sort::Perm)
    }
    pub fn perm_perm_div(&self, a: Term, b: Term) -> Term {
        self.check(&[&a, &b]);
        assert_eq!(b.sort(), &Sort::Perm);
        self.create(TermKind::PermPermDiv(a, b), Sort::Perm)
    }
    pub fn perm_div(&self, a: Term, b: Term) -> Term {
        self.perm_times(a, self.fraction_perm(self.int_literal(1), b))
    }
    pub fn perm_plus(&self, a: Term, b: Term) -> Term {
        self.check(&[&a, &b]);
        match (a.kind(), b.kind()) {
            (TermKind::NoPerm, _) => return b,
            (_, TermKind::NoPerm) => return a,
            _ => {}
        }
        if let (Some(x), Some(y)) = (Self::permission_literal(&a), Self::permission_literal(&b)) {
            return self.fraction_perm_literal(x + y);
        }
        match (a.kind(), b.kind()) {
            (TermKind::FractionPerm(n1, d1), TermKind::FractionPerm(n2, d2)) if d1 == d2 => {
                self.fraction_perm(self.plus(n1.clone(), n2.clone()), d1.clone())
            }
            (TermKind::PermMinus(x, y), _) if y == &b => x.clone(),
            (_, TermKind::PermMinus(x, y)) if y == &a => x.clone(),
            (TermKind::PermNegation(x), _) => self.perm_minus(b.clone(), x.clone()),
            (_, TermKind::PermNegation(x)) => self.perm_minus(a.clone(), x.clone()),
            _ => self.create(TermKind::PermPlus(a, b), Sort::Perm),
        }
    }
    pub fn perm_minus(&self, a: Term, b: Term) -> Term {
        self.check(&[&a, &b]);
        if matches!(b.kind(), TermKind::NoPerm) {
            return a;
        }
        if a == b {
            return self.no_perm();
        }
        if let (Some(x), Some(y)) = (Self::permission_literal(&a), Self::permission_literal(&b)) {
            return self.fraction_perm_literal(x - y);
        }
        match (a.kind(), b.kind()) {
            (_, TermKind::PermMinus(x, y)) if &a == x => y.clone(),
            (TermKind::PermPlus(x, y), _) if x == &b => y.clone(),
            (TermKind::PermPlus(x, y), _) if y == &b => x.clone(),
            (_, TermKind::PermNegation(x)) => self.perm_plus(a.clone(), x.clone()),
            _ => self.create(TermKind::PermMinus(a, b), Sort::Perm),
        }
    }
    pub fn perm_negation(&self, p: Term) -> Term {
        self.check(&[&p]);
        match p.kind() {
            TermKind::PermNegation(inner) => inner.clone(),
            TermKind::NoPerm => p,
            _ => self.create(TermKind::PermNegation(p), Sort::Perm),
        }
    }
    pub fn perm_less(&self, a: Term, b: Term) -> Term {
        self.check(&[&a, &b]);
        if a == b {
            return self.boolean(false);
        }
        if let (Some(x), Some(y)) = (Self::permission_literal(&a), Self::permission_literal(&b)) {
            return self.boolean(x < y);
        }
        if let TermKind::Ite(c, x, y) = b.kind() {
            return self.ite(
                c.clone(),
                self.perm_less(a.clone(), x.clone()),
                self.perm_less(a.clone(), y.clone()),
            );
        }
        self.create(TermKind::PermLess(a, b), Sort::Bool)
    }
    pub fn perm_at_most(&self, a: Term, b: Term) -> Term {
        self.check(&[&a, &b]);
        if let (Some(x), Some(y)) = (Self::permission_literal(&a), Self::permission_literal(&b)) {
            return self.boolean(x <= y);
        }
        if a == b {
            return self.boolean(true);
        }
        self.create(TermKind::PermAtMost(a, b), Sort::Bool)
    }
    pub fn perm_min(&self, a: Term, b: Term) -> Term {
        self.check(&[&a, &b]);
        if a == b {
            return a;
        }
        if let (Some(x), Some(y)) = (Self::permission_literal(&a), Self::permission_literal(&b)) {
            return if x > y { b } else { a };
        }
        assert_eq!(a.sort(), &Sort::Perm);
        assert_eq!(b.sort(), &Sort::Perm);
        self.create(TermKind::PermMin(a, b), Sort::Perm)
    }
}

impl TermFactory {
    fn seq_element(term: &Term) -> Sort {
        match term.sort() {
            Sort::Seq(element) => (**element).clone(),
            _ => panic!("expected sequence sort"),
        }
    }
    pub fn seq_ranged(&self, low: Term, high: Term) -> Term {
        self.check(&[&low, &high]);
        assert_eq!(low.sort(), &Sort::Int);
        assert_eq!(high.sort(), &Sort::Int);
        self.create(
            TermKind::SeqRanged(low, high),
            Sort::Seq(Box::new(Sort::Int)),
        )
    }
    pub fn seq_nil(&self, element: Sort) -> Term {
        self.create(
            TermKind::SeqNil(element.clone()),
            Sort::Seq(Box::new(element)),
        )
    }
    pub fn seq_singleton(&self, element: Term) -> Term {
        self.check(&[&element]);
        let sort = Sort::Seq(Box::new(element.sort().clone()));
        self.create(TermKind::SeqSingleton(element), sort)
    }
    pub fn seq_append(&self, a: Term, b: Term) -> Term {
        self.check(&[&a, &b]);
        Self::seq_element(&a);
        assert_eq!(a.sort(), b.sort());
        let sort = a.sort().clone();
        self.create(TermKind::SeqAppend(a, b), sort)
    }
    pub fn seq_drop(&self, seq: Term, count: Term) -> Term {
        self.check(&[&seq, &count]);
        Self::seq_element(&seq);
        assert_eq!(count.sort(), &Sort::Int);
        let sort = seq.sort().clone();
        self.create(TermKind::SeqDrop(seq, count), sort)
    }
    pub fn seq_take(&self, seq: Term, count: Term) -> Term {
        self.check(&[&seq, &count]);
        Self::seq_element(&seq);
        assert_eq!(count.sort(), &Sort::Int);
        let sort = seq.sort().clone();
        self.create(TermKind::SeqTake(seq, count), sort)
    }
    pub fn seq_length(&self, seq: Term) -> Term {
        self.check(&[&seq]);
        Self::seq_element(&seq);
        self.create(TermKind::SeqLength(seq), Sort::Int)
    }
    pub fn seq_at(&self, seq: Term, index: Term) -> Term {
        self.check(&[&seq, &index]);
        let sort = Self::seq_element(&seq);
        assert_eq!(index.sort(), &Sort::Int);
        self.create(TermKind::SeqAt(seq, index), sort)
    }
    pub fn seq_in(&self, seq: Term, value: Term) -> Term {
        self.seq_in_impl(seq, value, false)
    }
    pub fn seq_in_trigger(&self, seq: Term, value: Term) -> Term {
        self.seq_in_impl(seq, value, true)
    }
    fn seq_in_impl(&self, seq: Term, value: Term, trigger: bool) -> Term {
        self.check(&[&seq, &value]);
        assert_eq!(&Self::seq_element(&seq), value.sort());
        self.create(
            if trigger {
                TermKind::SeqInTrigger(seq, value)
            } else {
                TermKind::SeqIn(seq, value)
            },
            Sort::Bool,
        )
    }
    pub fn seq_update(&self, seq: Term, index: Term, value: Term) -> Term {
        self.check(&[&seq, &index, &value]);
        assert_eq!(index.sort(), &Sort::Int);
        assert_eq!(&Self::seq_element(&seq), value.sort());
        if self.options.use_old_axiomatization {
            let sort = seq.sort().clone();
            self.create(TermKind::SeqUpdate(seq, index, value), sort)
        } else {
            self.seq_append(
                self.seq_take(seq.clone(), index.clone()),
                self.seq_append(
                    self.seq_singleton(value),
                    self.seq_drop(seq, self.plus(index, self.int_literal(1))),
                ),
            )
        }
    }
}

impl TermFactory {
    fn set_element(term: &Term) -> Sort {
        match term.sort() {
            Sort::Set(s) => (**s).clone(),
            _ => panic!("expected set sort"),
        }
    }
    fn multiset_element(term: &Term) -> Sort {
        match term.sort() {
            Sort::Multiset(s) => (**s).clone(),
            _ => panic!("expected multiset sort"),
        }
    }
    pub fn empty_set(&self, element: Sort) -> Term {
        self.create(
            TermKind::EmptySet(element.clone()),
            Sort::Set(Box::new(element)),
        )
    }
    pub fn singleton_set(&self, value: Term) -> Term {
        self.check(&[&value]);
        let sort = Sort::Set(Box::new(value.sort().clone()));
        self.create(TermKind::SingletonSet(value), sort)
    }
    pub fn set_add(&self, set: Term, value: Term) -> Term {
        self.check(&[&set, &value]);
        assert_eq!(&Self::set_element(&set), value.sort());
        let sort = set.sort().clone();
        self.create(TermKind::SetAdd(set, value), sort)
    }
    pub fn set_union(&self, a: Term, b: Term) -> Term {
        self.check(&[&a, &b]);
        Self::set_element(&a);
        assert_eq!(a.sort(), b.sort());
        let sort = a.sort().clone();
        self.create(TermKind::SetUnion(a, b), sort)
    }
    pub fn set_intersection(&self, a: Term, b: Term) -> Term {
        self.check(&[&a, &b]);
        Self::set_element(&a);
        assert_eq!(a.sort(), b.sort());
        let sort = a.sort().clone();
        self.create(TermKind::SetIntersection(a, b), sort)
    }
    pub fn set_subset(&self, a: Term, b: Term) -> Term {
        self.check(&[&a, &b]);
        Self::set_element(&a);
        assert_eq!(a.sort(), b.sort());
        let sort = Sort::Bool;
        self.create(TermKind::SetSubset(a, b), sort)
    }
    pub fn set_difference(&self, a: Term, b: Term) -> Term {
        self.check(&[&a, &b]);
        Self::set_element(&a);
        assert_eq!(a.sort(), b.sort());
        let sort = a.sort().clone();
        self.create(TermKind::SetDifference(a, b), sort)
    }
    pub fn set_disjoint(&self, a: Term, b: Term) -> Term {
        self.check(&[&a, &b]);
        Self::set_element(&a);
        assert_eq!(a.sort(), b.sort());
        let sort = Sort::Bool;
        self.create(TermKind::SetDisjoint(a, b), sort)
    }
    pub fn set_cardinality(&self, set: Term) -> Term {
        self.check(&[&set]);
        Self::set_element(&set);
        self.create(TermKind::SetCardinality(set), Sort::Int)
    }
    pub fn empty_multiset(&self, element: Sort) -> Term {
        self.create(
            TermKind::EmptyMultiset(element.clone()),
            Sort::Multiset(Box::new(element)),
        )
    }
    pub fn singleton_multiset(&self, value: Term) -> Term {
        self.check(&[&value]);
        let sort = Sort::Multiset(Box::new(value.sort().clone()));
        self.create(TermKind::SingletonMultiset(value), sort)
    }
    pub fn multiset_add(&self, set: Term, value: Term) -> Term {
        self.check(&[&set, &value]);
        assert_eq!(&Self::multiset_element(&set), value.sort());
        let sort = set.sort().clone();
        self.create(TermKind::MultisetAdd(set, value), sort)
    }
    pub fn multiset_union(&self, a: Term, b: Term) -> Term {
        self.check(&[&a, &b]);
        Self::multiset_element(&a);
        assert_eq!(a.sort(), b.sort());
        let sort = a.sort().clone();
        self.create(TermKind::MultisetUnion(a, b), sort)
    }
    pub fn multiset_intersection(&self, a: Term, b: Term) -> Term {
        self.check(&[&a, &b]);
        Self::multiset_element(&a);
        assert_eq!(a.sort(), b.sort());
        let sort = a.sort().clone();
        self.create(TermKind::MultisetIntersection(a, b), sort)
    }
    pub fn multiset_subset(&self, a: Term, b: Term) -> Term {
        self.check(&[&a, &b]);
        Self::multiset_element(&a);
        assert_eq!(a.sort(), b.sort());
        let sort = Sort::Bool;
        self.create(TermKind::MultisetSubset(a, b), sort)
    }
    pub fn multiset_difference(&self, a: Term, b: Term) -> Term {
        self.check(&[&a, &b]);
        Self::multiset_element(&a);
        assert_eq!(a.sort(), b.sort());
        let sort = a.sort().clone();
        self.create(TermKind::MultisetDifference(a, b), sort)
    }
    pub fn multiset_cardinality(&self, set: Term) -> Term {
        self.check(&[&set]);
        Self::multiset_element(&set);
        self.create(TermKind::MultisetCardinality(set), Sort::Int)
    }
    pub fn set_in(&self, value: Term, set: Term) -> Term {
        self.check(&[&value, &set]);
        assert_eq!(&Self::set_element(&set), value.sort());
        self.create(TermKind::SetIn(value, set), Sort::Bool)
    }
    pub fn multiset_count(&self, set: Term, value: Term) -> Term {
        self.check(&[&set, &value]);
        assert_eq!(&Self::multiset_element(&set), value.sort());
        self.create(TermKind::MultisetCount(set, value), Sort::Int)
    }
}

impl TermFactory {
    fn map_sorts(map: &Term) -> (Sort, Sort) {
        match map.sort() {
            Sort::Map(k, v) => ((**k).clone(), (**v).clone()),
            _ => panic!("expected map sort"),
        }
    }
    pub fn empty_map(&self, key: Sort, value: Sort) -> Term {
        let sort = Sort::Map(Box::new(key.clone()), Box::new(value.clone()));
        self.create(TermKind::EmptyMap(key, value), sort)
    }
    pub fn map_lookup(&self, map: Term, key: Term) -> Term {
        self.check(&[&map, &key]);
        let (k, v) = Self::map_sorts(&map);
        assert_eq!(&k, key.sort());
        self.create(TermKind::MapLookup(map, key), v)
    }
    pub fn map_cardinality(&self, map: Term) -> Term {
        self.check(&[&map]);
        Self::map_sorts(&map);
        self.create(TermKind::MapCardinality(map), Sort::Int)
    }
    pub fn map_update(&self, map: Term, key: Term, value: Term) -> Term {
        self.check(&[&map, &key, &value]);
        let (k, v) = Self::map_sorts(&map);
        assert_eq!(&k, key.sort());
        assert_eq!(&v, value.sort());
        let sort = map.sort().clone();
        self.create(TermKind::MapUpdate(map, key, value), sort)
    }
    pub fn map_domain(&self, map: Term) -> Term {
        self.check(&[&map]);
        let (k, _) = Self::map_sorts(&map);
        self.create(TermKind::MapDomain(map), Sort::Set(Box::new(k)))
    }
    pub fn map_range(&self, map: Term) -> Term {
        self.check(&[&map]);
        let (_, v) = Self::map_sorts(&map);
        self.create(TermKind::MapRange(map), Sort::Set(Box::new(v)))
    }
}

impl TermFactory {
    pub fn sort_wrapper(&self, term: Term, to: Sort) -> Term {
        self.check(&[&term]);
        if term.sort() == &to {
            return term;
        }
        if let TermKind::SortWrapper(inner, _) = term.kind() {
            if inner.sort() == &to {
                return inner.clone();
            }
        }
        assert!(
            term.sort() == &Sort::Snap || to == Sort::Snap,
            "sort wrappers require a Snap endpoint"
        );
        self.create(TermKind::SortWrapper(term, to.clone()), to)
    }
    pub fn combine(&self, a: Term, b: Term) -> Term {
        self.check(&[&a, &b]);
        let a = self.sort_wrapper(a, Sort::Snap);
        let b = self.sort_wrapper(b, Sort::Snap);
        self.create(TermKind::Combine(a, b), Sort::Snap)
    }
    pub fn first(&self, snap: Term) -> Term {
        self.check(&[&snap]);
        if let TermKind::Combine(a, _) = snap.kind() {
            return a.clone();
        }
        assert_eq!(snap.sort(), &Sort::Snap);
        self.create(TermKind::First(snap), Sort::Snap)
    }
    pub fn second(&self, snap: Term) -> Term {
        self.check(&[&snap]);
        if let TermKind::Combine(_, b) = snap.kind() {
            return b.clone();
        }
        assert_eq!(snap.sort(), &Sort::Snap);
        self.create(TermKind::Second(snap), Sort::Snap)
    }
    pub fn to_snap_tree(&self, args: impl IntoIterator<Item = Term>) -> Term {
        let mut args = args.into_iter().map(|a| self.sort_wrapper(a, Sort::Snap));
        match args.next() {
            None => self.unit(),
            Some(first) => args.fold(first, |a, b| self.combine(a, b)),
        }
    }
    pub fn from_snap_tree(&self, snap: Term, size: i32) -> Vec<Term> {
        self.check(&[&snap]);
        if size <= 1 {
            return vec![snap];
        }
        let mut result = self.from_snap_tree(self.first(snap.clone()), size - 1);
        result.push(self.second(snap));
        result
    }
    pub fn from_snap_tree_targets(&self, snap: Term, targets: &[Term]) -> Vec<Term> {
        self.check(&targets.iter().collect::<Vec<_>>());
        let size = i32::try_from(targets.len()).expect("too many snapshot targets");
        self.from_snap_tree(snap, size)
            .into_iter()
            .zip(targets)
            .map(|(part, target)| self.sort_wrapper(part, target.sort().clone()))
            .collect()
    }
    pub fn magic_wand_snapshot(&self, mwsf: Term) -> Term {
        self.check(&[&mwsf]);
        assert_eq!(mwsf.sort(), &Sort::MagicWandSnapFunction);
        self.create(
            TermKind::MagicWandSnapshot(mwsf),
            Sort::MagicWandSnapFunction,
        )
    }
    /// Apply the underlying wand function to the consumed left-hand snapshot.
    pub fn apply_wand_snapshot(&self, snapshot: &Term, lhs: Term) -> Term {
        self.check(&[snapshot, &lhs]);
        let TermKind::MagicWandSnapshot(mwsf) = snapshot.kind() else {
            panic!("expected a magic wand snapshot");
        };
        self.mwsf_lookup(mwsf.clone(), lhs)
    }
    /// Yield the token guarding the recorded package conditions for this snapshot.
    pub fn yield_wand_token(&self, snapshot: &Term, lhs: Term) -> Term {
        self.check(&[snapshot, &lhs]);
        let TermKind::MagicWandSnapshot(mwsf) = snapshot.kind() else {
            panic!("expected a magic wand snapshot");
        };
        self.magic_wand_token(mwsf.clone(), lhs)
    }
    pub fn mwsf_lookup(&self, mwsf: Term, snap: Term) -> Term {
        self.check(&[&mwsf, &snap]);
        assert_eq!(mwsf.sort(), &Sort::MagicWandSnapFunction);
        assert_eq!(snap.sort(), &Sort::Snap);
        self.create(TermKind::MwsfLookup(mwsf, snap), Sort::Snap)
    }
    pub fn magic_wand_token(&self, mwsf: Term, snap: Term) -> Term {
        self.check(&[&mwsf, &snap]);
        assert_eq!(mwsf.sort(), &Sort::MagicWandSnapFunction);
        assert_eq!(snap.sort(), &Sort::Snap);
        self.create(TermKind::MagicWandToken(mwsf, snap), Sort::Bool)
    }
}

impl TermFactory {
    fn fvf_sort(fvf: &Term) -> Sort {
        match fvf.sort() {
            Sort::FieldValueFunction { codomain, .. } => (**codomain).clone(),
            _ => panic!("expected field value function"),
        }
    }
    fn psf_sort(psf: &Term) -> Sort {
        match psf.sort() {
            Sort::PredicateSnapFunction { codomain, .. } => (**codomain).clone(),
            _ => panic!("expected predicate snapshot function"),
        }
    }
    pub fn lookup(&self, field: String, fvf: Term, at: Term) -> Term {
        self.check(&[&fvf, &at]);
        let sort = Self::fvf_sort(&fvf);
        assert_eq!(at.sort(), &Sort::Ref);
        self.create(TermKind::Lookup(field, fvf, at), sort)
    }
    pub fn perm_lookup(&self, field: String, pm: Term, at: Term) -> Term {
        self.check(&[&pm, &at]);
        assert_eq!(pm.sort(), &Sort::FieldPermFunction);
        assert_eq!(at.sort(), &Sort::Ref);
        self.create(TermKind::PermLookup(field, pm, at), Sort::Perm)
    }
    pub fn domain(&self, field: String, fvf: Term) -> Term {
        self.check(&[&fvf]);
        Self::fvf_sort(&fvf);
        self.create(TermKind::Domain(field, fvf), Sort::Set(Box::new(Sort::Ref)))
    }
    pub fn has_domain(&self, field: String, fvf: Term, is_global: bool) -> Term {
        self.check(&[&fvf]);
        Self::fvf_sort(&fvf);
        self.create(TermKind::HasDomain(field, fvf, is_global), Sort::Bool)
    }
    pub fn field_trigger(&self, field: String, fvf: Term, at: Term) -> Term {
        self.check(&[&fvf, &at]);
        Self::fvf_sort(&fvf);
        assert_eq!(at.sort(), &Sort::Ref);
        self.create(TermKind::FieldTrigger(field, fvf, at), Sort::Bool)
    }
    pub fn predicate_lookup(&self, name: String, psf: Term, args: Vec<Term>) -> Term {
        self.check(&[&psf]);
        self.check(&args.iter().collect::<Vec<_>>());
        let sort = Self::psf_sort(&psf);
        self.create(TermKind::PredicateLookup(name, psf, args), sort)
    }
    pub fn predicate_perm_lookup(&self, name: String, pm: Term, args: Vec<Term>) -> Term {
        self.check(&[&pm]);
        self.check(&args.iter().collect::<Vec<_>>());
        assert_eq!(pm.sort(), &Sort::PredicatePermFunction);
        self.create(TermKind::PredicatePermLookup(name, pm, args), Sort::Perm)
    }
    pub fn predicate_domain(&self, name: String, psf: Term) -> Term {
        self.check(&[&psf]);
        Self::psf_sort(&psf);
        self.create(
            TermKind::PredicateDomain(name, psf),
            Sort::Set(Box::new(Sort::Snap)),
        )
    }
    pub fn has_predicate_domain(&self, name: String, psf: Term, is_global: bool) -> Term {
        self.check(&[&psf]);
        Self::psf_sort(&psf);
        self.create(
            TermKind::HasPredicateDomain(name, psf, is_global),
            Sort::Bool,
        )
    }
    pub fn predicate_trigger(&self, name: String, psf: Term, args: Vec<Term>) -> Term {
        self.check(&[&psf]);
        self.check(&args.iter().collect::<Vec<_>>());
        Self::psf_sort(&psf);
        self.create(TermKind::PredicateTrigger(name, psf, args), Sort::Bool)
    }
}

impl TermFactory {
    fn is_zero_mask(term: &Term) -> bool {
        matches!(term.kind(), TermKind::ZeroMask | TermKind::PredZeroMask)
    }
    pub fn heap_lookup(&self, heap: Term, at: Term) -> Term {
        self.check(&[&heap, &at]);
        match heap.kind() {
            TermKind::ZeroMask | TermKind::PredZeroMask => return self.no_perm(),
            TermKind::HeapSingleton(location, value, _)
            | TermKind::HeapUpdate(_, location, value)
                if location == &at =>
            {
                return value.clone();
            }
            TermKind::MergeSingle(_, mask, location, value)
                if location == &at && Self::is_zero_mask(mask) =>
            {
                return value.clone();
            }
            TermKind::MaskAdd(mask, location, value)
                if location == &at && Self::is_zero_mask(mask) =>
            {
                return value.clone();
            }
            _ => {}
        }
        let sort = match heap.sort() {
            Sort::PredHeap => Sort::Snap,
            Sort::PredMask => Sort::Perm,
            Sort::Heap(value) => (**value).clone(),
            Sort::WandHeap => Sort::MagicWandSnapFunction,
            _ => panic!("expected heap sort"),
        };
        self.create(TermKind::HeapLookup(heap, at), sort)
    }
    pub fn heap_update(&self, heap: Term, at: Term, value: Term) -> Term {
        self.check(&[&heap, &at, &value]);
        let sort = heap.sort().clone();
        self.create(TermKind::HeapUpdate(heap, at, value), sort)
    }
    pub fn mask_add(&self, mask: Term, at: Term, addition: Term) -> Term {
        self.check(&[&mask, &at, &addition]);
        if matches!(addition.kind(), TermKind::NoPerm) {
            return mask;
        }
        if let TermKind::MaskAdd(inner, previous_at, previous_addition) = mask.kind() {
            if previous_at == &at {
                return self.mask_add(
                    inner.clone(),
                    at,
                    self.perm_plus(addition, previous_addition.clone()),
                );
            }
            if let (
                TermKind::MaskAdd(base, first_at, first_addition),
                TermKind::PermNegation(sub),
            ) = (inner.kind(), addition.kind())
            {
                if first_at == &at {
                    return self.mask_add(
                        self.mask_add(
                            base.clone(),
                            first_at.clone(),
                            self.perm_minus(first_addition.clone(), sub.clone()),
                        ),
                        previous_at.clone(),
                        previous_addition.clone(),
                    );
                }
            }
        }
        assert_eq!(
            at.sort(),
            if mask.sort() == &Sort::PredMask {
                &Sort::Snap
            } else {
                &Sort::Ref
            }
        );
        assert_eq!(addition.sort(), &Sort::Perm);
        let sort = mask.sort().clone();
        self.create(TermKind::MaskAdd(mask, at, addition), sort)
    }
    pub fn heap_singleton(&self, at: Term, value: Term, sort: Sort) -> Term {
        self.check(&[&at, &value]);
        self.create(TermKind::HeapSingleton(at, value, sort.clone()), sort)
    }
    pub fn identical_on_known_locations(&self, old: Term, new: Term, mask: Term) -> Term {
        self.check(&[&old, &new, &mask]);
        if Self::is_zero_mask(&mask) {
            return self.boolean(true);
        }
        self.create(
            TermKind::IdenticalOnKnownLocations(old, new, mask),
            Sort::Bool,
        )
    }
    pub fn good_mask(&self, mask: Term) -> Term {
        self.check(&[&mask]);
        if Self::is_zero_mask(&mask) {
            return self.boolean(true);
        }
        self.create(TermKind::GoodMask(mask), Sort::Bool)
    }
    pub fn good_field_mask(&self, mask: Term, upper_bound: bool) -> Term {
        self.check(&[&mask]);
        if Self::is_zero_mask(&mask) {
            return self.boolean(true);
        }
        self.create(TermKind::GoodFieldMask(mask, upper_bound), Sort::Bool)
    }
    pub fn merge_single(&self, heap: Term, mask: Term, at: Term, value: Term) -> Term {
        self.check(&[&heap, &mask, &at, &value]);
        if Self::is_zero_mask(&mask) {
            return self.heap_singleton(at, value, heap.sort().clone());
        }
        if let TermKind::HeapLookup(h, l) = value.kind() {
            if h == &heap && l == &at {
                return heap;
            }
        }
        let sort = heap.sort().clone();
        self.create(TermKind::MergeSingle(heap, mask, at, value), sort)
    }
    pub fn merge_heaps(&self, h1: Term, m1: Term, h2: Term, m2: Term) -> Term {
        self.check(&[&h1, &m1, &h2, &m2]);
        if Self::is_zero_mask(&m1) {
            return h2;
        }
        if Self::is_zero_mask(&m2) || h1 == h2 {
            return h1;
        }
        let sort = h1.sort().clone();
        self.create(TermKind::MergeHeaps(h1, m1, h2, m2), sort)
    }
    pub fn heaps_overlap(&self, h1: Term, m1: Term, h2: Term, m2: Term) -> Term {
        self.check(&[&h1, &m1, &h2, &m2]);
        if Self::is_zero_mask(&m1) {
            return h2;
        }
        if Self::is_zero_mask(&m2) {
            return h1;
        }
        if h1 == h2 {
            return self.boolean(true);
        }
        let sort = h1.sort().clone();
        self.create(TermKind::HeapsOverlap(h1, m1, h2, m2), sort)
    }
    pub fn mask_eq(&self, a: Term, b: Term) -> Term {
        self.check(&[&a, &b]);
        self.create(TermKind::MaskEq(a, b), Sort::Bool)
    }
    pub fn mask_sum(&self, a: Term, b: Term) -> Term {
        self.check(&[&a, &b]);
        if Self::is_zero_mask(&a) {
            return b;
        }
        if Self::is_zero_mask(&b) {
            return a;
        }
        if let TermKind::MaskDiff(zero, m) = a.kind() {
            if Self::is_zero_mask(zero) {
                return self.mask_diff(b.clone(), m.clone());
            }
        }
        let sort = a.sort().clone();
        self.create(TermKind::MaskSum(a, b), sort)
    }
    pub fn mask_diff(&self, a: Term, b: Term) -> Term {
        self.check(&[&a, &b]);
        if Self::is_zero_mask(&b) {
            return a;
        }
        if let TermKind::MaskSum(m, last) = a.kind() {
            if last == &b {
                return m.clone();
            }
        }
        let sort = a.sort().clone();
        self.create(TermKind::MaskDiff(a, b), sort)
    }
    pub fn dummy_heap(&self, sort: Sort) -> Term {
        self.create(TermKind::DummyHeap(sort.clone()), sort)
    }
}

impl TermFactory {
    fn declaration(&self, kind: DeclarationKind) -> Declaration {
        if !self.options.use_flyweight {
            return Declaration(Arc::new(DeclarationNode {
                kind,
                flyweight: false,
            }));
        }
        let mut pool = DECLARATION_POOL
            .get_or_init(|| Mutex::new(HashMap::new()))
            .lock()
            .expect("declaration flyweight pool poisoned");
        Declaration(
            pool.entry(kind.clone())
                .or_insert_with(|| {
                    Arc::new(DeclarationNode {
                        kind,
                        flyweight: true,
                    })
                })
                .clone(),
        )
    }
    pub fn sort_decl(&self, sort: Sort) -> Declaration {
        self.declaration(DeclarationKind::Sort(sort))
    }
    pub fn function_decl(&self, fun: Applicable) -> Declaration {
        self.function_decl_target(ApplicationTarget::Function(fun))
    }
    pub fn function_decl_target(&self, target: ApplicationTarget) -> Declaration {
        match &target {
            ApplicationTarget::Function(fun) => {
                assert_ne!(
                    fun.data().kind,
                    ApplicableKind::Macro,
                    "macro is not a function"
                );
                assert_eq!(
                    fun.uses_flyweight(),
                    self.options.use_flyweight,
                    "cannot mix flyweight modes"
                );
            }
            ApplicationTarget::Variable(var) => {
                self.check(&[var]);
                assert!(
                    matches!(var.kind(), TermKind::Var(_)),
                    "expected a variable"
                );
            }
        }
        self.declaration(DeclarationKind::Function(target))
    }
    pub fn const_decl(&self, var: Term) -> Declaration {
        self.function_decl_target(ApplicationTarget::Variable(var))
    }
    pub fn sort_wrapper_decl(&self, from: Sort, to: Sort) -> Declaration {
        self.declaration(DeclarationKind::SortWrapper(from, to))
    }
    pub fn macro_decl(&self, id: Identifier, args: Vec<Term>, body: Term) -> Declaration {
        self.check(&[&body]);
        self.check(&args.iter().collect::<Vec<_>>());
        assert!(
            args.iter().all(|t| matches!(t.kind(), TermKind::Var(_))),
            "macro parameters must be variables"
        );
        self.declaration(DeclarationKind::Macro { id, args, body })
    }
}

impl TermFactory {
    pub fn app_var(&self, var: Term, args: Vec<Term>) -> Term {
        self.check(&[&var]);
        self.check(&args.iter().collect::<Vec<_>>());
        assert!(
            matches!(var.kind(), TermKind::Var(_)),
            "expected a variable"
        );
        assert_eq!(
            args.len(),
            1,
            "variable applicable expects one Unit argument"
        );
        assert_eq!(args[0].sort(), &Sort::Unit);
        let sort = var.sort().clone();
        self.create(
            TermKind::App {
                applicable: ApplicationTarget::Variable(var),
                args,
            },
            sort,
        )
    }
    pub fn app_hint(&self, applicable: Applicable) -> Term {
        assert_eq!(
            applicable.uses_flyweight(),
            self.options.use_flyweight,
            "cannot mix flyweight modes"
        );
        let sort = applicable.data().result_sort.clone();
        self.create(
            TermKind::AppHint(ApplicationTarget::Function(applicable)),
            sort,
        )
    }
    pub fn app_hint_var(&self, var: Term) -> Term {
        self.check(&[&var]);
        assert!(
            matches!(var.kind(), TermKind::Var(_)),
            "expected a variable"
        );
        let sort = var.sort().clone();
        self.create(TermKind::AppHint(ApplicationTarget::Variable(var)), sort)
    }
}

static FORALL_COUNTER: AtomicI32 = AtomicI32::new(0);
static QUANTIFICATION_COUNTER: AtomicI32 = AtomicI32::new(0);

impl TermFactory {
    pub fn forall_default_name() -> String {
        format!("quant-u-{}", FORALL_COUNTER.fetch_add(1, Ordering::Relaxed))
    }
    pub fn quantification_default_name() -> String {
        format!(
            "quant-{}",
            QUANTIFICATION_COUNTER.fetch_add(1, Ordering::Relaxed)
        )
    }
    /// Construct a quantification with no triggers; `quantification` handles trigger rewriting
    /// and filtering for nonempty trigger lists.
    pub fn quantification_without_triggers(
        &self,
        quantifier: Quantifier,
        vars: Vec<Term>,
        body: Term,
        name: String,
        is_global: bool,
        weight: Option<i32>,
    ) -> Term {
        self.check(&[&body]);
        self.check(&vars.iter().collect::<Vec<_>>());
        assert!(
            vars.iter().all(|v| matches!(v.kind(), TermKind::Var(_))),
            "quantifier binders must be variables"
        );
        self.create(
            TermKind::Quantification {
                quantifier,
                vars,
                body,
                triggers: Vec::new(),
                name,
                is_global,
                weight,
            },
            Sort::Bool,
        )
    }
    pub fn simplifying_forall_without_triggers(
        &self,
        vars: Vec<Term>,
        body: Term,
        name: String,
    ) -> Term {
        self.check(&[&body]);
        self.check(&vars.iter().collect::<Vec<_>>());
        match body.kind() {
            TermKind::True => return self.boolean(true),
            TermKind::False if !vars.is_empty() => return self.boolean(false),
            _ => {}
        }
        if vars.is_empty() {
            return body;
        }
        self.quantification_without_triggers(Quantifier::Forall, vars, body, name, false, None)
    }
}

/// Upstream traversal has no case for some heap operations; report those explicitly.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct UnsupportedSubterms(pub &'static str);
impl fmt::Display for UnsupportedSubterms {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "upstream subterms has no case for {}", self.0)
    }
}
impl std::error::Error for UnsupportedSubterms {}
impl Term {
    pub fn visit(&self, f: &mut impl FnMut(&Term)) -> Result<(), UnsupportedSubterms> {
        f(self);
        for child in self.subterms()? {
            child.visit(f)?;
        }
        Ok(())
    }
    pub fn visit_opt(&self, f: &mut impl FnMut(&Term) -> bool) -> Result<(), UnsupportedSubterms> {
        if f(self) {
            for child in self.subterms()? {
                child.visit_opt(f)?;
            }
        }
        Ok(())
    }
    pub fn reduce_tree<R>(
        &self,
        f: &mut impl FnMut(&Term, Vec<R>) -> R,
    ) -> Result<R, UnsupportedSubterms> {
        let children = self
            .subterms()?
            .iter()
            .map(|t| t.reduce_tree(f))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(f(self, children))
    }
    pub fn find<R>(
        &self,
        f: &mut impl FnMut(&Term) -> Option<R>,
    ) -> Result<Option<R>, UnsupportedSubterms> {
        if let Some(value) = f(self) {
            return Ok(Some(value));
        }
        for child in self.subterms()? {
            if let Some(value) = child.find(f)? {
                return Ok(Some(value));
            }
        }
        Ok(None)
    }
    pub fn contains(&self, needle: &Term) -> Result<bool, UnsupportedSubterms> {
        Ok(self
            .find(&mut |term| (term == needle).then_some(()))?
            .is_some())
    }
    pub fn has_subterm(&self, needle: &Term) -> Result<bool, UnsupportedSubterms> {
        Ok(self
            .find(&mut |term| (term == needle && term != self).then_some(()))?
            .is_some())
    }
    pub fn deep_collect<R>(
        &self,
        f: &mut impl FnMut(&Term) -> Option<R>,
    ) -> Result<Vec<R>, UnsupportedSubterms> {
        let children = self
            .subterms()?
            .iter()
            .map(|t| t.deep_collect(f))
            .collect::<Result<Vec<_>, _>>()?;
        let mut result = Vec::new();
        if let Some(value) = f(self) {
            result.push(value);
        }
        result.extend(children.into_iter().flatten());
        Ok(result)
    }
    pub fn shallow_collect<R>(
        &self,
        f: &mut impl FnMut(&Term) -> Option<R>,
    ) -> Result<Vec<R>, UnsupportedSubterms> {
        if let Some(value) = f(self) {
            return Ok(vec![value]);
        }
        let mut result = Vec::new();
        for child in self.subterms()? {
            result.extend(child.shallow_collect(f)?);
        }
        Ok(result)
    }
    /// Free variables in first-encounter order; quantifier binders are removed after
    /// collecting their body and triggers, as in upstream's tree reduction.
    pub fn free_variables(&self) -> Result<InsertionOrderedSet<Term>, UnsupportedSubterms> {
        let mut result = InsertionOrderedSet::new();
        for child in self.subterms()? {
            for var in child.free_variables()? {
                result = result.incl(var);
            }
        }
        match self.kind() {
            TermKind::Var(_) => result = result.incl(self.clone()),
            TermKind::Let(bindings, _) => {
                for (var, _) in bindings.iter() {
                    result = result.excl(var);
                }
            }
            TermKind::Quantification { vars, .. } => {
                for var in vars {
                    result = result.excl(var);
                }
            }
            _ => {}
        }
        Ok(result)
    }
    pub fn top_level_conjuncts(&self) -> Vec<Term> {
        match self.kind() {
            TermKind::And(ts) => ts.iter().flat_map(Term::top_level_conjuncts).collect(),
            _ => vec![self.clone()],
        }
    }
    pub fn subterms(&self) -> Result<Vec<Term>, UnsupportedSubterms> {
        let terms = match self.kind() {
            TermKind::Unit
            | TermKind::Null
            | TermKind::ZeroMask
            | TermKind::PredZeroMask
            | TermKind::True
            | TermKind::False
            | TermKind::NoPerm
            | TermKind::FullPerm
            | TermKind::IntLiteral(_)
            | TermKind::Var(_)
            | TermKind::FractionPermLiteral(_)
            | TermKind::SeqNil(_)
            | TermKind::EmptySet(_)
            | TermKind::EmptyMultiset(_)
            | TermKind::DummyHeap(_)
            | TermKind::EmptyMap(_, _) => vec![],
            TermKind::Not(a)
            | TermKind::IsValidPermVal(a)
            | TermKind::IsReadPermVar(a)
            | TermKind::PermNegation(a)
            | TermKind::SeqSingleton(a)
            | TermKind::SeqLength(a)
            | TermKind::SingletonSet(a)
            | TermKind::SetCardinality(a)
            | TermKind::SingletonMultiset(a)
            | TermKind::MultisetCardinality(a)
            | TermKind::MapCardinality(a)
            | TermKind::MapDomain(a)
            | TermKind::MapRange(a)
            | TermKind::First(a)
            | TermKind::Second(a)
            | TermKind::MagicWandSnapshot(a)
            | TermKind::GoodMask(a)
            | TermKind::SortWrapper(a, _)
            | TermKind::Domain(_, a)
            | TermKind::HasDomain(_, a, _)
            | TermKind::PredicateDomain(_, a)
            | TermKind::HasPredicateDomain(_, a, _)
            | TermKind::GoodFieldMask(a, _) => vec![a.clone()],
            TermKind::Plus(a, b)
            | TermKind::Minus(a, b)
            | TermKind::Times(a, b)
            | TermKind::Div(a, b)
            | TermKind::Mod(a, b)
            | TermKind::Implies(a, b)
            | TermKind::Iff(a, b)
            | TermKind::BuiltinEquals(a, b)
            | TermKind::CustomEquals(a, b)
            | TermKind::Less(a, b)
            | TermKind::AtMost(a, b)
            | TermKind::Greater(a, b)
            | TermKind::AtLeast(a, b)
            | TermKind::FractionPerm(a, b)
            | TermKind::PermTimes(a, b)
            | TermKind::IntPermTimes(a, b)
            | TermKind::PermIntDiv(a, b)
            | TermKind::PermPermDiv(a, b)
            | TermKind::PermPlus(a, b)
            | TermKind::PermMinus(a, b)
            | TermKind::PermLess(a, b)
            | TermKind::PermAtMost(a, b)
            | TermKind::PermMin(a, b)
            | TermKind::SeqRanged(a, b)
            | TermKind::SeqAppend(a, b)
            | TermKind::SeqDrop(a, b)
            | TermKind::SeqTake(a, b)
            | TermKind::SeqAt(a, b)
            | TermKind::SeqIn(a, b)
            | TermKind::SeqInTrigger(a, b)
            | TermKind::SetAdd(a, b)
            | TermKind::SetUnion(a, b)
            | TermKind::SetIntersection(a, b)
            | TermKind::SetSubset(a, b)
            | TermKind::SetDisjoint(a, b)
            | TermKind::SetDifference(a, b)
            | TermKind::SetIn(a, b)
            | TermKind::MultisetAdd(a, b)
            | TermKind::MultisetUnion(a, b)
            | TermKind::MultisetIntersection(a, b)
            | TermKind::MultisetSubset(a, b)
            | TermKind::MultisetDifference(a, b)
            | TermKind::MultisetCount(a, b)
            | TermKind::MapLookup(a, b)
            | TermKind::Combine(a, b)
            | TermKind::MwsfLookup(a, b)
            | TermKind::MagicWandToken(a, b)
            | TermKind::HeapLookup(a, b)
            | TermKind::MaskSum(a, b)
            | TermKind::MaskDiff(a, b)
            | TermKind::Lookup(_, a, b)
            | TermKind::PermLookup(_, a, b)
            | TermKind::FieldTrigger(_, a, b)
            | TermKind::HeapSingleton(a, b, _) => vec![a.clone(), b.clone()],
            TermKind::Ite(a, b, c)
            | TermKind::SeqUpdate(a, b, c)
            | TermKind::MapUpdate(a, b, c)
            | TermKind::HeapUpdate(a, b, c)
            | TermKind::MaskAdd(a, b, c)
            | TermKind::IdenticalOnKnownLocations(a, b, c) => vec![a.clone(), b.clone(), c.clone()],
            TermKind::Or(ts) | TermKind::And(ts) | TermKind::App { args: ts, .. } => ts.clone(),
            TermKind::PredicateLookup(_, psf, args)
            | TermKind::PredicatePermLookup(_, psf, args)
            | TermKind::PredicateTrigger(_, psf, args) => {
                let mut ts = vec![psf.clone()];
                ts.extend(args.iter().cloned());
                ts
            }
            TermKind::Quantification {
                vars,
                body,
                triggers,
                ..
            } => {
                let mut ts = vars.clone();
                ts.push(body.clone());
                ts.extend(triggers.iter().flat_map(|t| t.terms.iter().cloned()));
                ts
            }
            // Upstream subterms omits the MergeSingle location.
            TermKind::MergeSingle(heap, mask, _, value) => {
                vec![heap.clone(), mask.clone(), value.clone()]
            }
            TermKind::MergeHeaps(a, b, c, d) | TermKind::HeapsOverlap(a, b, c, d) => {
                vec![a.clone(), b.clone(), c.clone(), d.clone()]
            }
            TermKind::HeapToSnap(heap, mask, _) => vec![heap.clone(), mask.clone()],
            TermKind::SnapToHeap(snap, _, _) => vec![snap.clone()],
            TermKind::MaskMapTerm(_) => return Err(UnsupportedSubterms("MaskMapTerm")),
            TermKind::HeapMapTerm(_) => return Err(UnsupportedSubterms("HeapMapTerm")),
            TermKind::Distinct(_) => vec![],
            TermKind::Let(bindings, body) => {
                let mut ts: Vec<_> = bindings.iter().map(|(v, _)| v.clone()).collect();
                ts.extend(bindings.iter().map(|(_, t)| t.clone()));
                ts.push(body.clone());
                ts
            }
            TermKind::MaskEq(..) => return Err(UnsupportedSubterms("MaskEq")),
            TermKind::AppHint(_) => return Err(UnsupportedSubterms("AppHint")),
        };
        Ok(terms)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct UnsupportedTriggerTransform(pub &'static str);
impl fmt::Display for UnsupportedTriggerTransform {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "upstream term transform has no case for {}", self.0)
    }
}
impl std::error::Error for UnsupportedTriggerTransform {}
impl TermFactory {
    fn rewrite_trigger_seq_in(&self, t: &Term) -> Result<Term, UnsupportedTriggerTransform> {
        self.transform_replacements(t, None)
    }
    /// Apply simultaneous pre-order replacements, stopping below each matched node.
    pub fn replace(
        &self,
        term: &Term,
        replacements: &HashMap<Term, Term>,
    ) -> Result<Term, UnsupportedTriggerTransform> {
        self.check(&[term]);
        for (from, to) in replacements {
            self.check(&[from, to]);
        }
        if replacements.is_empty() {
            return Ok(term.clone());
        }
        self.transform_replacements(term, Some(replacements))
    }
    fn transform_replacements(
        &self,
        t: &Term,
        replacements: Option<&HashMap<Term, Term>>,
    ) -> Result<Term, UnsupportedTriggerTransform> {
        if let Some(replacements) = replacements {
            if let Some(replacement) = replacements.get(t) {
                return Ok(replacement.clone());
            }
        }
        let go = |x: &Term| self.transform_replacements(x, replacements);
        let result = match t.kind() {
            // Trigger rewriting is pre-order and stops recursion at the matched SeqIn.
            TermKind::SeqIn(a, b) if replacements.is_none() => {
                self.seq_in_trigger(a.clone(), b.clone())
            }
            TermKind::SeqIn(a, b) => self.seq_in(go(a)?, go(b)?),
            TermKind::Unit
            | TermKind::Null
            | TermKind::ZeroMask
            | TermKind::PredZeroMask
            | TermKind::True
            | TermKind::False
            | TermKind::NoPerm
            | TermKind::FullPerm
            | TermKind::IntLiteral(_)
            | TermKind::Var(_)
            | TermKind::FractionPermLiteral(_)
            | TermKind::SeqNil(_)
            | TermKind::EmptySet(_)
            | TermKind::EmptyMultiset(_)
            | TermKind::DummyHeap(_)
            | TermKind::AppHint(_)
            | TermKind::EmptyMap(_, _) => t.clone(),
            TermKind::Not(a) => self.not(go(a)?),
            TermKind::IsValidPermVal(a) => self.is_valid_perm_val(go(a)?),
            TermKind::IsReadPermVar(a) => self.is_read_perm_var(go(a)?),
            TermKind::PermNegation(a) => self.perm_negation(go(a)?),
            TermKind::SeqSingleton(a) => self.seq_singleton(go(a)?),
            TermKind::SeqLength(a) => self.seq_length(go(a)?),
            TermKind::SingletonSet(a) => self.singleton_set(go(a)?),
            TermKind::SetCardinality(a) => self.set_cardinality(go(a)?),
            TermKind::SingletonMultiset(a) => self.singleton_multiset(go(a)?),
            TermKind::MultisetCardinality(a) => self.multiset_cardinality(go(a)?),
            TermKind::MapCardinality(a) => self.map_cardinality(go(a)?),
            TermKind::MapDomain(a) => self.map_domain(go(a)?),
            TermKind::MapRange(a) => self.map_range(go(a)?),
            TermKind::First(a) => self.first(go(a)?),
            TermKind::Second(a) => self.second(go(a)?),
            TermKind::MagicWandSnapshot(a) => self.magic_wand_snapshot(go(a)?),
            TermKind::GoodMask(a) => self.good_mask(go(a)?),
            TermKind::Plus(a, b) => self.plus(go(a)?, go(b)?),
            TermKind::Minus(a, b) => self.minus(go(a)?, go(b)?),
            TermKind::Times(a, b) => self.times(go(a)?, go(b)?),
            TermKind::Div(a, b) => self.div(go(a)?, go(b)?),
            TermKind::Mod(a, b) => self.modulo(go(a)?, go(b)?),
            TermKind::Implies(a, b) => self.implies(go(a)?, go(b)?),
            TermKind::Iff(a, b) => self.iff(go(a)?, go(b)?),
            TermKind::Less(a, b) => self.less(go(a)?, go(b)?),
            TermKind::AtMost(a, b) => self.at_most(go(a)?, go(b)?),
            TermKind::Greater(a, b) => self.greater(go(a)?, go(b)?),
            TermKind::AtLeast(a, b) => self.at_least(go(a)?, go(b)?),
            TermKind::FractionPerm(a, b) => self.fraction_perm(go(a)?, go(b)?),
            TermKind::PermTimes(a, b) => self.perm_times(go(a)?, go(b)?),
            TermKind::IntPermTimes(a, b) => self.int_perm_times(go(a)?, go(b)?),
            TermKind::PermIntDiv(a, b) => self.perm_int_div(go(a)?, go(b)?),
            TermKind::PermPermDiv(a, b) => self.perm_perm_div(go(a)?, go(b)?),
            TermKind::PermPlus(a, b) => self.perm_plus(go(a)?, go(b)?),
            TermKind::PermMinus(a, b) => self.perm_minus(go(a)?, go(b)?),
            TermKind::PermLess(a, b) => self.perm_less(go(a)?, go(b)?),
            TermKind::PermAtMost(a, b) => self.perm_at_most(go(a)?, go(b)?),
            TermKind::PermMin(a, b) => self.perm_min(go(a)?, go(b)?),
            TermKind::SeqRanged(a, b) => self.seq_ranged(go(a)?, go(b)?),
            TermKind::SeqAppend(a, b) => self.seq_append(go(a)?, go(b)?),
            TermKind::SeqDrop(a, b) => self.seq_drop(go(a)?, go(b)?),
            TermKind::SeqTake(a, b) => self.seq_take(go(a)?, go(b)?),
            TermKind::SeqAt(a, b) => self.seq_at(go(a)?, go(b)?),
            TermKind::SeqInTrigger(a, b) => self.seq_in_trigger(go(a)?, go(b)?),
            TermKind::SetAdd(a, b) => self.set_add(go(a)?, go(b)?),
            TermKind::SetUnion(a, b) => self.set_union(go(a)?, go(b)?),
            TermKind::SetIntersection(a, b) => self.set_intersection(go(a)?, go(b)?),
            TermKind::SetSubset(a, b) => self.set_subset(go(a)?, go(b)?),
            TermKind::SetDisjoint(a, b) => self.set_disjoint(go(a)?, go(b)?),
            TermKind::SetDifference(a, b) => self.set_difference(go(a)?, go(b)?),
            TermKind::SetIn(a, b) => self.set_in(go(a)?, go(b)?),
            TermKind::MultisetAdd(a, b) => self.multiset_add(go(a)?, go(b)?),
            TermKind::MultisetUnion(a, b) => self.multiset_union(go(a)?, go(b)?),
            TermKind::MultisetIntersection(a, b) => self.multiset_intersection(go(a)?, go(b)?),
            TermKind::MultisetSubset(a, b) => self.multiset_subset(go(a)?, go(b)?),
            TermKind::MultisetDifference(a, b) => self.multiset_difference(go(a)?, go(b)?),
            TermKind::MultisetCount(a, b) => self.multiset_count(go(a)?, go(b)?),
            TermKind::MapLookup(a, b) => self.map_lookup(go(a)?, go(b)?),
            TermKind::Combine(a, b) => self.combine(go(a)?, go(b)?),
            TermKind::MwsfLookup(a, b) => self.mwsf_lookup(go(a)?, go(b)?),
            TermKind::MagicWandToken(a, b) => self.magic_wand_token(go(a)?, go(b)?),
            TermKind::HeapLookup(a, b) => self.heap_lookup(go(a)?, go(b)?),
            TermKind::MaskSum(a, b) => self.mask_sum(go(a)?, go(b)?),
            TermKind::MaskDiff(a, b) => self.mask_diff(go(a)?, go(b)?),
            TermKind::Ite(a, b, c) => self.ite(go(a)?, go(b)?, go(c)?),
            TermKind::SeqUpdate(a, b, c) => self.seq_update(go(a)?, go(b)?, go(c)?),
            TermKind::MapUpdate(a, b, c) => self.map_update(go(a)?, go(b)?, go(c)?),
            TermKind::HeapUpdate(a, b, c) => self.heap_update(go(a)?, go(b)?, go(c)?),
            TermKind::MaskAdd(a, b, c) => self.mask_add(go(a)?, go(b)?, go(c)?),
            TermKind::IdenticalOnKnownLocations(a, b, c) => {
                self.identical_on_known_locations(go(a)?, go(b)?, go(c)?)
            }
            TermKind::BuiltinEquals(a, b) => {
                let left = go(a)?;
                let right = go(b)?;
                assert_eq!(
                    left.sort(),
                    a.sort(),
                    "unexpected equality operand sort change"
                );
                self.builtin_equals(left, right)
            }
            TermKind::CustomEquals(a, b) => {
                let left = go(a)?;
                let right = go(b)?;
                assert_eq!(
                    left.sort(),
                    a.sort(),
                    "unexpected equality operand sort change"
                );
                self.create(TermKind::CustomEquals(left, right), Sort::Bool)
            }
            TermKind::Or(ts) => self.or(ts.iter().map(go).collect::<Result<Vec<_>, _>>()?),
            TermKind::And(ts) => self.and(ts.iter().map(go).collect::<Result<Vec<_>, _>>()?),
            TermKind::App { applicable, args } => {
                let args = args.iter().map(go).collect::<Result<Vec<_>, _>>()?;
                match applicable {
                    ApplicationTarget::Function(f) => self.app(f.clone(), args),
                    ApplicationTarget::Variable(v) => self.app_var(v.clone(), args),
                }
            }
            TermKind::SortWrapper(a, sort) => self.sort_wrapper(go(a)?, sort.clone()),
            TermKind::Lookup(name, a, b) => self.lookup(name.clone(), go(a)?, go(b)?),
            TermKind::PermLookup(name, a, b) => self.perm_lookup(name.clone(), go(a)?, go(b)?),
            TermKind::FieldTrigger(name, a, b) => self.field_trigger(name.clone(), go(a)?, go(b)?),
            TermKind::Domain(name, a) => self.domain(name.clone(), go(a)?),
            TermKind::HasDomain(name, a, g) => self.has_domain(name.clone(), go(a)?, *g),
            TermKind::PredicateDomain(name, a) => self.predicate_domain(name.clone(), go(a)?),
            TermKind::HasPredicateDomain(name, a, g) => {
                self.has_predicate_domain(name.clone(), go(a)?, *g)
            }
            TermKind::PredicateLookup(name, a, args) => self.predicate_lookup(
                name.clone(),
                go(a)?,
                args.iter().map(go).collect::<Result<Vec<_>, _>>()?,
            ),
            TermKind::PredicatePermLookup(name, a, args) => self.predicate_perm_lookup(
                name.clone(),
                go(a)?,
                args.iter().map(go).collect::<Result<Vec<_>, _>>()?,
            ),
            TermKind::PredicateTrigger(name, a, args) => self.predicate_trigger(
                name.clone(),
                go(a)?,
                args.iter().map(go).collect::<Result<Vec<_>, _>>()?,
            ),
            TermKind::GoodFieldMask(a, upper) => self.good_field_mask(go(a)?, *upper),
            TermKind::HeapSingleton(a, b, sort) => {
                self.heap_singleton(go(a)?, go(b)?, sort.clone())
            }
            TermKind::MergeSingle(a, b, c, d) => self.merge_single(go(a)?, go(b)?, go(c)?, go(d)?),
            TermKind::MergeHeaps(a, b, c, d) => self.merge_heaps(go(a)?, go(b)?, go(c)?, go(d)?),
            TermKind::HeapToSnap(heap, mask, resource) => {
                self.heap_to_snap(go(heap)?, go(mask)?, resource.clone())
            }
            TermKind::SnapToHeap(snap, resource, sort) => {
                self.snap_to_heap(go(snap)?, resource.clone(), sort.clone())
            }
            TermKind::MaskMapTerm(_) => return Err(UnsupportedTriggerTransform("MaskMapTerm")),
            TermKind::HeapMapTerm(_) => return Err(UnsupportedTriggerTransform("HeapMapTerm")),
            TermKind::Distinct(_) => t.clone(),
            TermKind::Let(bindings, body) => {
                let bindings = bindings
                    .iter()
                    .map(|(v, t)| Ok((go(v)?, go(t)?)))
                    .collect::<Result<Vec<_>, UnsupportedTriggerTransform>>()?;
                self.let_term(bindings, go(body)?)
            }
            TermKind::HeapsOverlap(..) => return Err(UnsupportedTriggerTransform("HeapsOverlap")),
            TermKind::MaskEq(..) => return Err(UnsupportedTriggerTransform("MaskEq")),
            TermKind::Quantification {
                quantifier,
                vars,
                body,
                triggers,
                name,
                is_global,
                weight,
            } => {
                let vars = vars.iter().map(go).collect::<Result<Vec<_>, _>>()?;
                let body = go(body)?;
                let triggers = triggers
                    .iter()
                    .map(|t| {
                        Ok(Trigger {
                            terms: t.terms.iter().map(go).collect::<Result<Vec<_>, _>>()?,
                        })
                    })
                    .collect::<Result<Vec<_>, UnsupportedTriggerTransform>>()?;
                self.quantification(
                    *quantifier,
                    vars,
                    body,
                    triggers,
                    name.clone(),
                    *is_global,
                    *weight,
                )?
            }
        };
        Ok(result)
    }
    fn is_possible_trigger(term: &Term) -> bool {
        match term.kind() {
            TermKind::App {
                applicable: ApplicationTarget::Function(f),
                ..
            } => f.data().kind != ApplicableKind::Macro,
            TermKind::App {
                applicable: ApplicationTarget::Variable(_),
                ..
            } => true,
            TermKind::CustomEquals(..)
            | TermKind::PermMin(..)
            | TermKind::SeqRanged(..)
            | TermKind::SeqNil(..)
            | TermKind::SeqSingleton(..)
            | TermKind::SeqAppend(..)
            | TermKind::SeqDrop(..)
            | TermKind::SeqTake(..)
            | TermKind::SeqUpdate(..)
            | TermKind::SeqLength(..)
            | TermKind::SeqAt(..)
            | TermKind::SeqIn(..)
            | TermKind::EmptySet(..)
            | TermKind::SingletonSet(..)
            | TermKind::SetAdd(..)
            | TermKind::SetUnion(..)
            | TermKind::SetIntersection(..)
            | TermKind::SetDifference(..)
            | TermKind::SetIn(..)
            | TermKind::SetCardinality(..)
            | TermKind::EmptyMultiset(..)
            | TermKind::SingletonMultiset(..)
            | TermKind::MultisetAdd(..)
            | TermKind::MultisetUnion(..)
            | TermKind::MultisetIntersection(..)
            | TermKind::MultisetDifference(..)
            | TermKind::MultisetCardinality(..)
            | TermKind::MultisetCount(..)
            | TermKind::MapLookup(..)
            | TermKind::MapCardinality(..)
            | TermKind::MapDomain(..)
            | TermKind::MapRange(..)
            | TermKind::MapUpdate(..)
            | TermKind::MwsfLookup(..)
            | TermKind::Unit
            | TermKind::Combine(..)
            | TermKind::First(..)
            | TermKind::Second(..)
            | TermKind::Domain(..)
            | TermKind::PredicateDomain(..)
            | TermKind::Lookup(..)
            | TermKind::PredicateLookup(..) => true,
            _ => false,
        }
    }
    pub fn simplifying_forall(
        &self,
        vars: Vec<Term>,
        body: Term,
        triggers: Vec<Trigger>,
    ) -> Result<Term, UnsupportedTriggerTransform> {
        self.check(&[&body]);
        self.check(&vars.iter().collect::<Vec<_>>());
        for trigger in &triggers {
            self.check(&trigger.terms.iter().collect::<Vec<_>>());
        }
        match body.kind() {
            TermKind::True => return Ok(self.boolean(true)),
            TermKind::False if !vars.is_empty() => return Ok(self.boolean(false)),
            _ => {}
        }
        if vars.is_empty() {
            return Ok(body);
        }
        self.quantification(
            Quantifier::Forall,
            vars,
            body,
            triggers,
            Self::forall_default_name(),
            false,
            None,
        )
    }
    pub fn quantification(
        &self,
        quantifier: Quantifier,
        vars: Vec<Term>,
        body: Term,
        triggers: Vec<Trigger>,
        name: String,
        is_global: bool,
        weight: Option<i32>,
    ) -> Result<Term, UnsupportedTriggerTransform> {
        self.check(&[&body]);
        self.check(&vars.iter().collect::<Vec<_>>());
        assert!(
            vars.iter().all(|v| matches!(v.kind(), TermKind::Var(_))),
            "quantifier binders must be variables"
        );
        for trigger in &triggers {
            self.check(&trigger.terms.iter().collect::<Vec<_>>());
        }
        let triggers = if self.options.use_old_axiomatization {
            triggers
        } else {
            let mut rewritten = Vec::new();
            for trigger in triggers {
                let transformed = Trigger {
                    terms: trigger
                        .terms
                        .iter()
                        .map(|t| self.rewrite_trigger_seq_in(t))
                        .collect::<Result<Vec<_>, _>>()?,
                };
                let changed = transformed != trigger;
                rewritten.push(trigger);
                if changed {
                    rewritten.push(transformed);
                }
            }
            if self.options.mask_heap_mode {
                rewritten.retain(|t| t.terms.iter().all(Self::is_possible_trigger));
            }
            rewritten
        };
        Ok(self.create(
            TermKind::Quantification {
                quantifier,
                vars,
                body,
                triggers,
                name,
                is_global,
                weight,
            },
            Sort::Bool,
        ))
    }
    pub fn custom_equals(&self, a: Term, b: Term) -> Term {
        self.check(&[&a, &b]);
        self.create(TermKind::CustomEquals(a, b), Sort::Bool)
    }
    pub fn instantiate(
        &self,
        quantification: &Term,
        terms: &[Term],
    ) -> Result<Term, UnsupportedTriggerTransform> {
        self.check(&[quantification]);
        let TermKind::Quantification { vars, body, .. } = quantification.kind() else {
            panic!("expected quantification")
        };
        assert_eq!(
            vars.len(),
            terms.len(),
            "wrong number of quantifier arguments"
        );
        let replacements = vars.iter().cloned().zip(terms.iter().cloned()).collect();
        self.replace(body, &replacements)
    }
    pub fn builtin_equals(&self, a: Term, b: Term) -> Term {
        self.check(&[&a, &b]);
        if matches!((a.kind(), b.kind()), (TermKind::Var(_), TermKind::Var(_))) && a == b {
            return self.boolean(true);
        }
        if let (Some(x), Some(y)) = (Self::permission_literal(&a), Self::permission_literal(&b)) {
            return self.boolean(x == y);
        }
        self.create(TermKind::BuiltinEquals(a, b), Sort::Bool)
    }
}

impl TermFactory {
    pub fn distinct(&self, functions: impl IntoIterator<Item = Applicable>) -> Term {
        let mut unique = Vec::new();
        for f in functions {
            assert_eq!(
                f.data().kind,
                ApplicableKind::DomainFun,
                "distinct requires domain functions"
            );
            assert_eq!(
                f.uses_flyweight(),
                self.options.use_flyweight,
                "cannot mix flyweight modes"
            );
            if !unique.contains(&f) {
                unique.push(f);
            }
        }
        if unique.len() < 2 {
            return self.boolean(true);
        }
        self.create(TermKind::Distinct(DomainFunctions(unique)), Sort::Bool)
    }
    pub fn let_term(&self, entries: impl IntoIterator<Item = (Term, Term)>, body: Term) -> Term {
        self.check(&[&body]);
        let mut unique: Vec<(Term, Term)> = Vec::new();
        for (var, value) in entries {
            self.check(&[&var, &value]);
            assert!(
                matches!(var.kind(), TermKind::Var(_)),
                "let binding requires a variable"
            );
            if let Some((_, old)) = unique.iter_mut().find(|(key, _)| key == &var) {
                *old = value;
            } else {
                unique.push((var, value));
            }
        }
        if unique.is_empty() {
            return body;
        }
        let sort = body.sort().clone();
        self.create(TermKind::Let(Bindings(unique), body), sort)
    }
}

impl TermFactory {
    pub fn predef_snapshot_var(&self) -> Term {
        self.var(Identifier::new("s@$"), Sort::Snap, false)
    }
    pub fn predef_receiver_var(&self) -> Term {
        self.var(Identifier::new("r"), Sort::Ref, false)
    }
    pub fn is_positive_perm(&self, term: Term) -> Term {
        self.check(&[&term]);
        if let Some(p) = Self::permission_literal(&term) {
            self.boolean(p > Rational::zero())
        } else {
            self.perm_less(self.no_perm(), term)
        }
    }
    pub fn is_nonpositive_perm(&self, term: Term) -> Term {
        self.check(&[&term]);
        if let Some(p) = Self::permission_literal(&term) {
            self.boolean(p <= Rational::zero())
        } else {
            self.or([
                self.equals(term.clone(), self.no_perm()),
                self.perm_less(term, self.no_perm()),
            ])
        }
    }
    pub fn is_nonnegative_perm(&self, term: Term) -> Term {
        self.check(&[&term]);
        self.or([
            self.equals(term.clone(), self.no_perm()),
            self.is_positive_perm(term),
        ])
    }
    pub fn big_perm_sum(&self, terms: impl IntoIterator<Item = Term>) -> Term {
        let mut terms = terms.into_iter();
        match terms.next() {
            None => self.no_perm(),
            Some(first) => terms.fold(first, |a, b| self.perm_plus(a, b)),
        }
    }
}
/// Silver-expression overloads preserve caller metadata on the comparison, while
/// the generated no-permission literal has Silver's default metadata.
pub fn is_positive_perm_exp(
    expr: ferrum_silver::ast::expression::Exp,
    metadata: ferrum_silver::ast::ast::Metadata,
) -> ferrum_silver::ast::expression::Exp {
    use ferrum_silver::ast::expression::{Exp, ExpKind};
    Exp::new(
        ExpKind::GtCmp(expr, Exp::new(ExpKind::NoPerm, Default::default())),
        metadata,
    )
}
pub fn is_nonpositive_perm_exp(
    expr: ferrum_silver::ast::expression::Exp,
    metadata: ferrum_silver::ast::ast::Metadata,
) -> ferrum_silver::ast::expression::Exp {
    use ferrum_silver::ast::expression::{Exp, ExpKind};
    Exp::new(
        ExpKind::LeCmp(expr, Exp::new(ExpKind::NoPerm, Default::default())),
        metadata,
    )
}
pub fn is_nonnegative_perm_exp(
    expr: ferrum_silver::ast::expression::Exp,
    metadata: ferrum_silver::ast::ast::Metadata,
) -> ferrum_silver::ast::expression::Exp {
    use ferrum_silver::ast::expression::{Exp, ExpKind};
    Exp::new(
        ExpKind::GeCmp(expr, Exp::new(ExpKind::NoPerm, Default::default())),
        metadata,
    )
}
/// Source's exact-read classification of symbolic permission expressions.
pub fn consume_exact_read(fp: &Term, constrainable: &InsertionOrderedSet<Term>) -> bool {
    match fp.kind() {
        TermKind::Var(_) => !constrainable.contains(fp),
        TermKind::PermPlus(a, b) | TermKind::PermMinus(a, b) | TermKind::PermMin(a, b) => {
            consume_exact_read(a, constrainable) || consume_exact_read(b, constrainable)
        }
        TermKind::PermTimes(a, b) | TermKind::PermPermDiv(a, b) => {
            consume_exact_read(a, constrainable) && consume_exact_read(b, constrainable)
        }
        TermKind::IntPermTimes(_, b) => consume_exact_read(b, constrainable),
        TermKind::PermIntDiv(a, _) => consume_exact_read(a, constrainable),
        TermKind::Ite(_, a, b) if matches!(b.kind(), TermKind::NoPerm) => {
            consume_exact_read(a, constrainable)
        }
        TermKind::Ite(_, a, b) if matches!(a.kind(), TermKind::NoPerm) => {
            consume_exact_read(b, constrainable)
        }
        TermKind::Ite(_, a, b) => {
            consume_exact_read(a, constrainable) || consume_exact_read(b, constrainable)
        }
        _ => true,
    }
}

impl TermFactory {
    pub fn heap_to_snap(&self, heap: Term, mask: Term, resource: ResourceKey) -> Term {
        self.check(&[&heap, &mask]);
        self.create(TermKind::HeapToSnap(heap, mask, resource), Sort::Snap)
    }
    pub fn snap_to_heap(&self, snap: Term, resource: ResourceKey, sort: Sort) -> Term {
        self.check(&[&snap]);
        if let TermKind::HeapToSnap(heap, _, source) = snap.kind() {
            assert_eq!(source, &resource, "snapshot resource mismatch");
            return heap.clone();
        }
        self.create(TermKind::SnapToHeap(snap, resource, sort.clone()), sort)
    }
    fn resource_map(&self, entries: impl IntoIterator<Item = (ResourceKey, Term)>) -> ResourceMap {
        let mut result: Vec<(ResourceKey, Term)> = Vec::new();
        for (key, value) in entries {
            self.check(&[&value]);
            if let Some((_, old)) = result.iter_mut().find(|(k, _)| k == &key) {
                *old = value;
            } else {
                result.push((key, value));
            }
        }
        ResourceMap(result)
    }
    pub fn mask_map_term(&self, entries: impl IntoIterator<Item = (ResourceKey, Term)>) -> Term {
        self.create(
            TermKind::MaskMapTerm(self.resource_map(entries)),
            Sort::Snap,
        )
    }
    pub fn heap_map_term(&self, entries: impl IntoIterator<Item = (ResourceKey, Term)>) -> Term {
        self.create(
            TermKind::HeapMapTerm(self.resource_map(entries)),
            Sort::Snap,
        )
    }
}

impl TermFactory {
    pub fn resource_trigger(
        &self,
        resource: &ResourceKey,
        snapshot_map: Term,
        mut args: Vec<Term>,
    ) -> Term {
        match resource {
            ResourceKey::Field(f) => {
                assert_eq!(args.len(), 1, "field resource requires one receiver");
                self.field_trigger(f.name.clone(), snapshot_map, args.remove(0))
            }
            ResourceKey::Predicate(p) => self.predicate_trigger(p.name.clone(), snapshot_map, args),
            ResourceKey::Wand(w) => self.predicate_trigger(w.to_string(), snapshot_map, args),
        }
    }
    pub fn resource_lookup(
        &self,
        resource: &ResourceKey,
        snapshot_map: Term,
        mut args: Vec<Term>,
    ) -> Term {
        match resource {
            ResourceKey::Field(f) => {
                assert_eq!(args.len(), 1, "field resource requires one receiver");
                self.lookup(f.name.clone(), snapshot_map, args.remove(0))
            }
            ResourceKey::Predicate(p) => self.predicate_lookup(p.name.clone(), snapshot_map, args),
            ResourceKey::Wand(w) => self.predicate_lookup(w.to_string(), snapshot_map, args),
        }
    }
    pub fn resource_permission_lookup(
        &self,
        resource: &ResourceKey,
        permission_map: Term,
        mut args: Vec<Term>,
    ) -> Term {
        match resource {
            ResourceKey::Field(f) => {
                assert_eq!(args.len(), 1, "field resource requires one receiver");
                self.perm_lookup(f.name.clone(), permission_map, args.remove(0))
            }
            ResourceKey::Predicate(p) => {
                self.predicate_perm_lookup(p.name.clone(), permission_map, args)
            }
            ResourceKey::Wand(w) => self.predicate_perm_lookup(w.to_string(), permission_map, args),
        }
    }
}

#[derive(Clone, Copy)]
enum Comparison {
    Less,
    AtMost,
    Greater,
    AtLeast,
}

impl TermFactory {
    pub fn less(&self, left: Term, right: Term) -> Term {
        self.compare(left, right, Comparison::Less)
    }
    pub fn at_most(&self, left: Term, right: Term) -> Term {
        self.compare(left, right, Comparison::AtMost)
    }
    pub fn greater(&self, left: Term, right: Term) -> Term {
        self.compare(left, right, Comparison::Greater)
    }
    pub fn at_least(&self, left: Term, right: Term) -> Term {
        self.compare(left, right, Comparison::AtLeast)
    }
    fn compare(&self, left: Term, right: Term, op: Comparison) -> Term {
        self.check(&[&left, &right]);
        if let (TermKind::IntLiteral(a), TermKind::IntLiteral(b)) = (left.kind(), right.kind()) {
            return self.boolean(match op {
                Comparison::Less => a < b,
                Comparison::AtMost => a <= b,
                Comparison::Greater => a > b,
                Comparison::AtLeast => a >= b,
            });
        }
        if let (Some(a), Some(b)) = (
            Self::permission_literal(&left),
            Self::permission_literal(&right),
        ) {
            return self.boolean(match op {
                Comparison::Less => a < b,
                Comparison::AtMost => a <= b,
                Comparison::Greater => a > b,
                Comparison::AtLeast => a >= b,
            });
        }
        if left == right {
            return self.boolean(matches!(op, Comparison::AtMost | Comparison::AtLeast));
        }
        if matches!(op, Comparison::Less) {
            assert_eq!(left.sort(), right.sort());
        }
        let kind = match op {
            Comparison::Less => TermKind::Less(left, right),
            Comparison::AtMost => TermKind::AtMost(left, right),
            Comparison::Greater => TermKind::Greater(left, right),
            Comparison::AtLeast => TermKind::AtLeast(left, right),
        };
        self.create(kind, Sort::Bool)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn factory(flyweight: bool) -> TermFactory {
        TermFactory::new(TermOptions {
            use_flyweight: flyweight,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        })
    }

    #[test]
    fn equality_modes_and_process_wide_pool() {
        let a = factory(true);
        let b = factory(true);
        let x = a.var(Identifier::new("x"), Sort::Int, false);
        let y = b.var(Identifier::new("x"), Sort::Int, false);
        assert!(x.ptr_eq(&y));
        let structural = factory(false);
        let x2 = structural.var(Identifier::new("x"), Sort::Int, false);
        let y2 = structural.var(Identifier::new("x"), Sort::Int, false);
        assert_eq!(x2, y2);
        assert!(!x2.ptr_eq(&y2));
        assert_ne!(x, x2);
    }

    #[test]
    fn source_case_objects_keep_identity_without_flyweights() {
        let left = factory(false);
        let right = factory(false);
        for (a, b) in [
            (left.unit(), right.unit()),
            (left.null(), right.null()),
            (left.boolean(true), right.boolean(true)),
            (left.boolean(false), right.boolean(false)),
            (left.zero_mask(), right.zero_mask()),
            (left.pred_zero_mask(), right.pred_zero_mask()),
            (left.no_perm(), right.no_perm()),
            (left.full_perm(), right.full_perm()),
        ] {
            assert!(a.ptr_eq(&b));
        }
    }

    #[test]
    fn const_decl_is_the_same_function_declaration_of_a_variable() {
        let f = factory(true);
        let var = f.var(Identifier::new("x"), Sort::Int, false);
        let constant = f.const_decl(var.clone());
        let function = f.function_decl_target(ApplicationTarget::Variable(var));
        assert!(constant.ptr_eq(&function));
        assert!(matches!(
            constant.kind(),
            DeclarationKind::Function(ApplicationTarget::Variable(_))
        ));
    }

    #[test]
    fn wand_snapshot_helpers_apply_the_underlying_function() {
        let f = factory(false);
        let function = f.var(Identifier::new("w"), Sort::MagicWandSnapFunction, false);
        let snapshot = f.magic_wand_snapshot(function.clone());
        let lhs = f.unit();
        assert!(
            matches!(f.apply_wand_snapshot(&snapshot, lhs.clone()).kind(),
            TermKind::MwsfLookup(actual, arg) if actual == &function && arg == &lhs)
        );
        assert!(matches!(f.yield_wand_token(&snapshot, lhs.clone()).kind(),
            TermKind::MagicWandToken(actual, arg) if actual == &function && arg == &lhs));
    }

    #[test]
    fn permission_zero_divisor_remains_symbolic_and_wildcards_choose_by_name() {
        let f = factory(false);
        let fraction = f.fraction_perm(f.int_literal(1), f.int_literal(0));
        assert!(matches!(fraction.kind(), TermKind::FractionPerm(_, _)));
        let a = f.var(Identifier::new("a"), Sort::Perm, true);
        let z = f.var(Identifier::new("z"), Sort::Perm, true);
        assert_eq!(f.wildcard_simplifying_perm_times(a, z.clone()), z);
    }

    #[test]
    fn resource_keys_preserve_structure_and_snap_roundtrip() {
        use ferrum_silver::ast::{ast::Metadata, r#type::Type};
        let f = factory(true);
        let int_field = ResourceKey::Field(Arc::new(Field {
            name: "f".into(),
            typ: Type::Int,
            meta: Metadata::default(),
        }));
        let bool_field = ResourceKey::Field(Arc::new(Field {
            name: "f".into(),
            typ: Type::Bool,
            meta: Metadata::default(),
        }));
        assert_ne!(int_field, bool_field);
        let heap = f.dummy_heap(Sort::Heap(Box::new(Sort::Int)));
        let snap = f.heap_to_snap(heap.clone(), f.zero_mask(), int_field.clone());
        assert_eq!(
            f.snap_to_heap(snap, int_field.clone(), Sort::Heap(Box::new(Sort::Int))),
            heap
        );
        let map = f.mask_map_term([(int_field, f.zero_mask()), (bool_field, f.zero_mask())]);
        if let TermKind::MaskMapTerm(entries) = map.kind() {
            assert_eq!(entries.iter().count(), 2);
        } else {
            panic!("expected mask map")
        }
    }

    #[test]
    fn heap_mask_simplification_and_zero_sized_snapshot_tree() {
        let f = factory(false);
        let location = f.var(Identifier::new("r"), Sort::Ref, false);
        let value = f.int_literal(42);
        let heap = f.heap_singleton(
            location.clone(),
            value.clone(),
            Sort::Heap(Box::new(Sort::Int)),
        );
        assert_eq!(f.heap_lookup(heap, location.clone()), value);
        let mask = f.mask_add(f.zero_mask(), location.clone(), f.full_perm());
        assert_eq!(f.heap_lookup(mask, location), f.full_perm());
        let snap = f.unit();
        assert_eq!(f.from_snap_tree(snap.clone(), 0), vec![snap]);
    }

    #[test]
    fn let_bindings_share_flyweight_independent_of_entry_order() {
        let f = factory(true);
        let x = f.var(Identifier::new("x"), Sort::Int, false);
        let y = f.var(Identifier::new("y"), Sort::Int, false);
        let a = f.let_term(
            [(x.clone(), f.int_literal(1)), (y.clone(), f.int_literal(2))],
            x.clone(),
        );
        let b = f.let_term([(y, f.int_literal(2)), (x.clone(), f.int_literal(1))], x);
        assert!(a.ptr_eq(&b));
    }

    #[test]
    fn app_hints_remain_structural_under_flyweight_mode() {
        let f = factory(true);
        let app = f.applicable(ApplicableData {
            kind: ApplicableKind::Fun,
            id: Identifier::new("f"),
            arg_sorts: vec![],
            result_sort: Sort::Int,
        });
        let left = f.app_hint(app.clone());
        let right = f.app_hint(app);
        assert_eq!(left, right);
        assert!(!left.ptr_eq(&right));
    }

    #[test]
    fn bindings_remove_bound_variables_and_instantiation_rewrites_body() {
        let f = factory(false);
        let x = f.var(Identifier::new("x"), Sort::Int, false);
        let y = f.var(Identifier::new("y"), Sort::Int, false);
        let body = f.plus(x.clone(), y.clone());
        let q = f.quantification_without_triggers(
            Quantifier::Forall,
            vec![x.clone()],
            body,
            "q".into(),
            false,
            None,
        );
        assert_eq!(
            q.free_variables()
                .unwrap()
                .iter()
                .cloned()
                .collect::<Vec<_>>(),
            vec![y.clone()]
        );
        assert_eq!(f.instantiate(&q, &[f.int_literal(0)]).unwrap(), y);
    }

    #[test]
    fn quantifier_seq_trigger_expansion_and_mask_filter() {
        let f = factory(false);
        let seq = f.var(Identifier::new("s"), Sort::Seq(Box::new(Sort::Int)), false);
        let x = f.var(Identifier::new("x"), Sort::Int, false);
        let membership = f.seq_in(seq, x.clone());
        let q = f
            .quantification(
                Quantifier::Forall,
                vec![x.clone()],
                f.boolean(true),
                vec![Trigger {
                    terms: vec![membership],
                }],
                "q".into(),
                false,
                None,
            )
            .unwrap();
        match q.kind() {
            TermKind::Quantification { triggers, .. } => {
                assert_eq!(triggers.len(), 2);
                assert!(matches!(
                    triggers[1].terms[0].kind(),
                    TermKind::SeqInTrigger(..)
                ));
            }
            _ => panic!("expected quantification"),
        }
        let mask = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: true,
        });
        let q = mask
            .quantification(
                Quantifier::Forall,
                vec![x.clone()],
                mask.boolean(true),
                vec![Trigger { terms: vec![x] }],
                "q".into(),
                false,
                None,
            )
            .unwrap();
        match q.kind() {
            TermKind::Quantification { triggers, .. } => assert!(triggers.is_empty()),
            _ => panic!("expected quantification"),
        }
    }

    #[test]
    fn junction_keeps_nested_terms_and_first_occurrences() {
        let f = factory(false);
        let x = f.var(Identifier::new("x"), Sort::Bool, false);
        let y = f.var(Identifier::new("y"), Sort::Bool, false);
        let nested = f.and([x.clone(), y.clone()]);
        let result = f.and([nested.clone(), x.clone(), nested.clone()]);
        assert_eq!(result.kind(), &TermKind::And(vec![nested, x]));
    }
}
