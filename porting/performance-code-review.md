# Code review of the nested iterator solver-work difference

The [comparable saturation experiment](performance-saturation.md) now tests
explicit weights and altered common-policy controls on two generated workloads.
It retains variability and does not promote a global default change.

The review produced three concrete hypotheses:
before-repetition saturation, one-worker solver ownership, and preamble ordering.
The first is an intentional upstream-version default change; the second is a
native execution-path difference; the third is visible in the captured SMT.
None has been established as the cause of the additional solver work.

This was a read-only code/trace review. It made no runtime changes and ran no
new profiling or verification. The [SMT comparison](performance-nested-smt.md)
remains the source of performance observations and repeated solver counters.

## Version scope and a stronger query match

Native production code is Ferrum `afdf10cf59106c38d09df32939f1aa9c77d0b989`.
The captured JVM bundle identifies Silicon
`6b540aa45e5af214f4727b7be463ce84b328fabd`, with Silver submodule
`f02e7010639f314447d74732146644565aa8d135`.
Ferrum's newer upstream port target is Silicon
`ff386aec4664231dc6f2cb56d8d35f1623088363`. The exact older Silicon tree was
available locally and extracted for comparison. Reviewed native files still
match their `afdf10c` blobs; source files match the `6b540aa4` tree. File/blob
hashes and the structural comparisons are in the
[machine record](performance-code-review.json). The
[annotated prover logs](evidence/nested-code-review/README.md) preserve the
high-level comments used to locate saturation checks.

The late depletion check is native command 13171 versus source-worker command
12918. Its immediately preceding negated quantified goal and `pTaken` macro
are token-identical after these six explicit fresh-symbol renamings:

| Native | Bundled source |
| --- | --- |
| `snapshot@137@main` | `$t@8@01` |
| `_1p@134@main` | `_1p@5@01` |
| `img@141@main` | `img@12@01` |
| `inv@140@main` | `inv@11@01` |
| `_resource_index0@549@main` | `_resource_index0@420@01` |
| `pTaken@550@main` | `pTaken@421@01` |

That is 261 macro tokens and 120 goal tokens, including identical local
quantifier annotations. Both checks have `rlimit=5000000` and return `unknown`.
Their recorded response waits were 0.471 and 0.032 seconds. Equality of the local
text does not establish that its free symbols have equivalent definitions or
that the solver contexts and histories are equivalent.

At this check, both sides have 1,528 active assertions, 753 `forall` occurrences,
911 patterns and the same 31-scope assertion-count vector. All **907 assertions
inside pushed scopes match positionwise under one consistent mapping of 278
fresh symbols**. The 621 root assertions have the same per-formula shape
multiset after locally normalizing fresh symbols and ignoring `:qid` annotations,
but their order differs. That weaker root comparison is not a proof of global
alpha-equivalence, equivalent declarations or identical solver behavior.

## 1. Before-repetition saturation is enabled only in the older bundle

Bundled `Config.scala:258–263` defaults `beforeRepetition` to `0.02`;
`Config.scala:304–325` scales nonzero weights with a 10 ms minimum. With the
default 100 ms base, this gives a 10 ms setting, represented by `rlimit=100000`
under the captured resource-bound policy. `QuantifiedChunkSupport.scala:1644`
requests that saturation immediately before iterating permission-removal
candidates. It asks Z3 to search the current context before subsequent checks.

Native [saturation defaults](../crates/ferrum-silicon/src/config.rs#L536) use
`before_repetition=0`; [the removal hook](../crates/ferrum-silicon/src/verifier/native_context.rs#L24443)
skips saturation when the computed option is absent. The newer `ff386aec`
upstream has the same zero default. Upstream commit
`ebba041bdd3a010959f9b1164f164a18ce97a223` deliberately disabled frequent
saturations because they could be expensive for generated programs. This is a
real difference from the benchmark bundle, not evidence of a mistranslated default.

The source worker log has **34** `State saturation: before repetition` checks;
native has none. One occurs immediately before source `pTaken@421`, where native
has no corresponding saturation. Source also has exactly 34 more `unknown`
responses at `rlimit=100000` than native, consistent with these extra calls.
An additional bounded search can change later search state and instantiation
behavior in either direction. Its presence does not prove that it helps this case.

The cheapest discriminating experiment is to hold all other settings fixed and
toggle only the before-repetition weight on each backend. Explicit weights
`[1,0.5,0.4,0,0]` versus `[1,0.5,0.4,0,0.02]` isolate that slot while keeping
after-inhale disabled. Check actual call placement, verified outcomes and Z3
work counters. Do not change a global default based on this one workload.

The older source also enables after-inhale saturation by default while native
and newer upstream disable it. No such calls were found in these captured logs,
so this second default difference has no demonstrated effect on the observed path.

## 2. Native's one-worker path retains the function-phase solver

The common native [orchestrator](../crates/ferrum-silicon/src/verifier/default_main_verifier.rs#L94)
calls `stop_main_prover`, emits worker contributions and queues methods after
function/predicate verification. In the
[single-context implementation](../crates/ferrum-silicon/src/verifier/native_context.rs#L18458),
`stop_main_prover` is a no-op, worker-preamble hooks are checkpoints, and
`queue_method` uses the same context. The one-worker/no-branch setup selects
that context in [the library entry point](../src/lib.rs#L1391).

Bundled `DefaultMainVerifier.scala:263–285` explicitly stops the owner prover and
queues methods on a pooled worker. The traces corroborate one native solver
versus source owner plus worker. At the aligned late check, native has 439
declared constants and 504 declared functions, versus 386 and 428 in the source
worker: **53 extra constants and 76 extra functions**, despite matching active
assertion counts and scope layout. Captured `global-decls=true` means popping
proof scopes does not erase all declaration history.

Retaining earlier declarations and search history could affect later term
insertion and heuristics. The existing offline experiment that removed 21
function-phase checks reduced native resource work by only about 2.1%; it
retained declarations, assertions and other history, so it does not simulate a
fresh worker and does not settle this hypothesis.

A discriminating test would construct a genuinely separate method solver with
the complete required worker preamble, keeping formulas and order controlled.
Capture all processes and compare results, diagnostics, contexts and work
counters. This is a more involved change than a saturation flag; simply resetting
the solver without restoring every required declaration and axiom is insufficient.

## 3. Root-axiom and declaration ordering differ

The 561 positionwise structural mismatches among the 1,528 active assertions all
occur in the root frame. The scoped assertions match under the consistent map.
The review observes differing assertion order and quantifier IDs. Root shape
multisets match under per-formula fresh-name normalization with `:qid` omitted;
this does not prove that every root difference is just a globally consistent
renaming and reorder or establish semantic equivalence of the two contexts.

For example, the native function axioms place
`mir_binop_Eq_UInt_usize_UInt_usize` before
`mir_unop_PtrMetadata_RawPtr_immutable_UInt_usize`; the source worker has the
reverse order. There is also a concrete sort-wrapper policy difference:
bundled `DefaultMainVerifier.scala:512–525` emits collection contributors before
domains, whereas the native
[general preamble](../crates/ferrum-silicon/src/verifier/native_preamble.rs#L1975)
lists domains before collections. Native
[collection ordering](../crates/ferrum-silicon/src/verifier/native_preamble.rs#L1858)
additionally sorts collected sorts by nesting depth. The corresponding native
context emits wrappers using this contributed order. This agrees with the
observed native domain wrapper preceding `Seq<Int>`, while the source has the
reverse order. It is a code-level ordering policy, rather than evidence of a
random hash iteration issue. Insertion order, quantifier IDs and generated names
can influence solver heuristics; their effect on this case remains unmeasured.

Both implementations' function-unit sorting uses descending call-graph height
and original program index: native
[function verification units](../crates/ferrum-silicon/src/supporters/functions/function_verification_unit.rs#L99)
and bundled `FunctionVerificationUnit.scala:93–99`. The reversal alone does not
identify a wrong sort; input member order, preamble contributors and traversal
order need tracing before attributing it to a particular implementation detail.

The discriminating test is an aligned, dependency-preserving preamble replay
with only wrapper contribution order changed, followed separately by a test of
function-axiom order if needed. Keep symbol correspondence explicit and compare
work counters and responses. Blindly stripping fresh-name suffixes or sorting
all commands would lose dependencies and would not isolate this hypothesis.

## Paths that did not yield a demonstrated mismatch

The inspected permission minimum, depletion/sufficiency checks, five-argument
`pTaken` macro construction, trigger serialization and relevant Boolean/equality
simplification follow the corresponding source rules. Both implementations also
cache effective solver limits and shortcut known-true terms; the extra resource
commands are not explained by a simple missing option cache. The review did not
establish a specific malformed trigger, accidental extra local macro argument or
different local depletion formula at the aligned check.

Chunk ordering, permission/snapshot cache keys and definition-assumption changes
remain secondary review targets. In particular, newer upstream changes some
inverse-axiom handling to `assumeDefinition`; those version differences require
checking path-condition ownership, not treating every difference from the older
bundle as a port defect. No causal mismatch was established in those paths here.

Start with the explicit saturation-weight experiment, then a controlled wrapper
reorder. Those can be investigated before the more involved method-solver
boundary change. These are hypotheses backed by code and traces, not validated
runtime optimizations.
