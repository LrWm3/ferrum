//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/Evaluator.scala
//!
//! Purpose:
//! Evaluate Silver expressions to symbolic terms with well-definedness checks.
//!
//! Planned Rust structure:
//! EvaluationRules and evaluator expose eval/evals/evalQuantified; eval3 wraps heap switching and
//! trigger recording, eval2 dispatches literals, locals, field/current-permission/forperm, old and
//! labelled old, let, boolean/conditional, integer and permission arithmetic,
//! domain/backend/function applications, quantified expressions, unfolding/applying/asserting,
//! sequences, sets/multisets and maps. Helpers cover sequence bounds, implication and short-circuit
//! joins, old-state evaluation, resource access, division, trigger evaluation, heap triggers and
//! value joins.
//!
//! Behavior to preserve:
//! Evaluate sequences left to right, retaining source debug expressions. Temporarily use wand
//! evaluation heap and clear reserve/exhale context, then restore; current permission reads
//! partially consumed heap. Missing old label fails; old evaluation restores heap and trigger
//! context. Wildcard uses full permission in read-only mode, otherwise fresh constrained ARP. Honor
//! strict versus short-circuit config, branch feasibility and join results. Check zero divisors,
//! sequence bounds and map membership unless trigger evaluation bypasses checks; final retry can
//! assume failed checks while combining errors. Quantified evaluation enters local solver scope,
//! binds fresh variables, evaluates guards before body/triggers, captures auxiliary assumptions,
//! restores selected state, and represents infeasible guard by absent body. Existential function
//! preconditions are universally assumed; invalid weights warn. Function applications consume
//! preconditions in a temporary store/heap, record snapshot, select limited opaque or revealed
//! function and restore state. Unfolding respects recursion limit, permissions and snapshot
//! restoration; applying uses wand rules. Trigger evaluation rolls back path conditions and error
//! count, restores successful deltas or warns and retains cached terms; heap trigger alternatives
//! form Cartesian products.
//!
//! Integration:
//! rules::consumer, producer, brancher, joiner, execution_flow_controller, heap_supporter,
//! predicate_supporter, magic_wand_supporter, state::terms/triggers and decider.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Continuation and verifier ownership, quantified auxiliary scopes, snapshot and error
//! propagation.
//!
//! Status: description only; implementation has not started.
