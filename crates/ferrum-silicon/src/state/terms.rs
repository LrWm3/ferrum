//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/state/Terms.scala
//!
//! Purpose:
//! Define Silicon symbolic terms, sort system, constructors and simplifications.
//!
//! Planned Rust structure:
//! Node, Symbol, Sort and sorts include primitive, collection, user/SMT, snapshot,
//! permission and heap/map sorts. Decl, Applicable, Function, Var, App and Macro model
//! solver symbols. Term traversal, freeVariables, replace and topLevelConjuncts connect
//! state::utils. ConditionalFlyweight and factory families govern construction;
//! StructuralEquality is retained as historical documentation while its unary
//! operator sibling is used by Trigger. Port literals, arithmetic, boolean and equality operators,
//! quantification/trigger/let, permission arithmetic, sequence/set/multiset/map terms,
//! snapshots and wand tokens, field/predicate value and permission maps, heap and mask
//! operations. Retain predef, perms, resource lookup/trigger, snapshot tree, sort assertion
//! and implicit conversion helpers.
//!
//! Construction groups to port in source order:
//! - SortDecl, FunctionDecl, SortWrapperDecl, MacroDecl, ConstDecl and
//!   SortWrapperId; Fun, HeapDepFun, DomainFun, SMTFun, Macro, Var, App and AppHint.
//! - Unit, IntLiteral, Null, ZeroMask, PredZeroMask and BooleanLiteral;
//!   Forall, Exists, SimplifyingForall and Quantification.
//! - Plus, Minus, Times, Div, Mod; Not, Or, And, Implies, Iff, Ite, Equals,
//!   BuiltinEquals, CustomEquals and comparisons.
//! - NoPerm, FullPerm, FractionPermLiteral/FractionPerm, IsValidPermVal,
//!   IsReadPermVar, PermTimes, WildcardSimplifyingPermTimes, IntPermTimes,
//!   PermIntDiv, PermPermDiv, PermDiv, PermPlus, PermMinus, PermNegation,
//!   PermLess, PermAtMost and PermMin.
//! - Sequence range/nil/singleton/append/drop/take/length/index/membership/update;
//!   set and multiset empty/singleton/add/union/intersection/subset/difference,
//!   membership or count, cardinality and set disjointness; map empty/lookup,
//!   cardinality/update/domain/range.
//! - Combine/First/Second, field and predicate domain/lookup/permission/trigger,
//!   MagicWandSnapshot, MWSFLookup, MagicWandToken and MagicWandChunkTerm.
//! - HeapLookup/Update/Singleton, HeapToSnap/SnapToHeap, masks and their maps,
//!   IdenticalOnKnownLocations, GoodMask/GoodFieldMask, MergeSingle/MergeHeaps,
//!   HeapsOverlap, MaskEq/Sum/Diff and DummyHeap. PsfAfterRelation and PsfTop
//!   are commented out upstream and do not define active terms.
//! - toSnapTree/fromSnapTree, ResourceTriggerFunction/ResourceLookup/
//!   ResourcePermissionLookup, SortWrapper, Distinct, Let, predef, perms and utils.
//!
//! Behavior to preserve:
//! Factories enforce sort constraints and implement local simplifications; reproduce each
//! source case and its order, including arbitrary-precision integer and exact permission
//! operations. ConditionalFlyweight uses identity equality/hash when configured and class
//! plus equalityDefiningMembers otherwise; factories conditionally pool. Preserve
//! quantifier metadata, ordered free variables and binder exclusion, built-in versus custom
//! equality, snapshot wrapping and resource-specific field/predicate/wand lookup. No global
//! new simplification or ordering normalization.
//!
//! useFlyweight is selected by the Z3-API configuration; factory pools use
//! getOrElseUpdate and remain allocated on companion factories.
//! Quantification retains name/global/weight in equality; default names use
//! counters. Unless old axiomatization is selected, SeqIn triggers gain a
//! transformed alternative; mask-heap mode additionally filters invalid sets.
//! And/Or currently compute flattened input then filter the original input,
//! apparently discarding flattening; preserve this observation for reconciliation
//! and differential testing, including deduplication order. SimplifyingForall
//! removes empty binders and simplifies true/false in its specified cases.
//! FractionPerm retains zero-denominator terms instead of evaluating them;
//! permission multiplication distributes through conditionals and sums.
//!
//! SeqUpdate retains its node under old axiomatization; otherwise it rewrites
//! to take, singleton and drop at index plus one. Combine converts both values
//! to Snap; First/Second eliminate a matching Combine. Collection constructors
//! enforce their operand and element sorts rather than merely recording them.
//!
//! Silver Rational compares normalized values but hashes the original numerator
//! and denominator; this apparent equality/hash inconsistency affects fraction
//! pool keys and needs reconciliation, not a silent correction. toSnapTree folds
//! left and returns Unit for empty input; fromSnapTree(size <= 1) returns the
//! supplied snapshot, including size zero. HasVarRepr carries mutable auxiliary
//! representation outside the equality-defining fields.
//!
//! Integration:
//! state::utils, state::triggers, state::chunks, state::symbol_converter; decider converters, rules and
//! supporters.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Term handles, equality/interning mode, factory lifetimes, solver caches and snapshot
//! ownership require reconciliation across these modules.
//!
//! Status: description only; implementation has not started.
