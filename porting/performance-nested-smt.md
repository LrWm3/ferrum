# Nested iterator SMT comparison

The subsequent [related-code review](performance-code-review.md) narrows the
follow-up hypotheses to saturation defaults, one-worker solver ownership and
preamble order, and checks structural equality at the late permission query.

Ferrum's captured SMT stream makes Z3 do more work on
`mut_element_nested_pass`, even though it issues fewer checks. Two solver-only
replays reproduced all original responses and the same work counters: compared
with Silicon's two streams, Ferrum caused **13.8% more quantifier instantiations
and 19.3% more resource-counter work**.

The original direct-Prusti observation was 80.17 seconds native versus 34.93
seconds JVM. This diagnostic parsed-Viper replay verified in **54.33 versus
51.77 seconds**, so it did not reproduce that end-to-end ratio. Subsequent
solver-only CPU timings varied substantially despite identical work counters.
These results identify a solver-work difference; they do not establish a stable
speed ratio or a specific faulty trigger/axiom.

## Input, backends and settings

Both retained Prusti dumps are byte-identical: 461,392 bytes, SHA-256
`9fbeab0cc9dc824772c9c5bfa06765a62998ca1141a56151b15f25068e38b3e7`.
The [preserved input](../tools/performance/fixtures/mut_element_nested_pass.vpr)
was replayed through Ferrum runtime `afdf10c` and the actual Prusti bundled
Silicon `6b540aa4`, with the same Z3 4.16 executable. The JVM jar hash is
`6d11d2b73efe97b97026050f13d966c5ec599cf70d43022346382e065a49cf7c`;
Z3 hash is `e583c4186a45e72411fa2cb2048401eed03f0f8e5f24694676a8f6271a50b765`.
This uses the bundled reference, not the newer standalone Silicon from the
broader compatibility study.

Both replays used one worker, branches off, internal caches on, a 180-second
program limit, 300-second outer watchdog, one reported error, more-complete
exhale, the termination plugin disabled, and Prusti's assertion/configuration
defaults. Existing adoption suites and ordinary background tasks continued.
The parsed frontend differs from Prusti's direct AST conversion path. Both
sessions verified with no errors, equal warning arrays and no pending supervised
cleanup. Production runtime code was unchanged.

The source's Boolean branch option is a flag with default false. An initial
attempt using `--parallelizeBranches=false` was rejected before verification;
it remains a failed attempt in the manifest. The valid source run omitted that
flag, matching the actual Prusti suite. Ferrum used explicit `false`.

Actual emitted SMT confirms matching base options and final overrides:
`smt.mbqi=false`, `smt.qi.eager_threshold=1000`, `model.partial=false`,
`smt.arith.solver=6`, and `smt.qi.max_multi_patterns=1000`. Base configuration
and preamble resources are byte-identical between the jar and Ferrum. Override
order differs, but every setting was acknowledged successfully and final values
agree before queries.

The traces use **resource limits**, not Z3 wall-clock `timeout` settings.
Both use the same set of `rlimit` values, but query counts and resource-setting
histories differ. The source sometimes keeps a value across consecutive checks;
Ferrum normally resets it to zero. Matching value sets alone do not establish
equal resource histories for corresponding queries.

## Commands and responses

A checked relay forwarded bytes unchanged and recorded command/response chunk
times. Each transcript passed contiguous-byte and command/response alignment
audits with no unmatched responses. Both drivers retained their own prover logs.

| Stream | Checks | `unsat` | `unknown` | Assertions | `forall` occurrences | Pattern occurrences | Check-response waits |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Ferrum | 1,111 | 719 | 392 | 3,951 | 928 | 1,023 | 16.911 s |
| Silicon owner | 22 | 7 | 15 | 764 | 600 | 663 | 0.046 s |
| Silicon worker | 1,193 | 712 | 481 | 3,802 | 928 | 1,023 | 11.500 s |

The native stream and source worker have equal aggregate quantifier/pattern
counts, but this does not establish identical formulas, triggers or solver
contexts. The native process carries function-phase and method-phase history in
one solver; source uses separate owner and method-worker solvers. Both produce
719 `unsat` responses in total. `unknown` responses occur in bounded auxiliary
checks and do not contradict the successful final verification outcomes.

Waits are measured from the relay receiving a chunk containing a command's end
to receiving the chunk containing its response's end. They include relay,
pipe and scheduling costs. They are not exclusive solver CPU and must not be
subtracted from total elapsed time as an exclusive frontend decomposition.

The slowest native check (command 13171) returned `unknown` after 0.471 seconds.
A structurally corresponding late quantified-permission check in the source
worker (12918) took 0.032 seconds. Both had `rlimit=5000000` and involved
`indexed_p_Param`, inverse/image functions, nested slice snapshots and a
quantified permission remainder. The next four response kinds also agree.
Their surrounding contexts and complete terms have not been proved equivalent;
this is a useful minimization target rather than an isolated causal comparison.

## Solver-only replay and stable counters

Each captured stdin stream was fed to a fresh identical Z3 process, followed by
`(get-info :all-statistics)`. All original output responses reproduced **exactly**;
the appended statistics were parsed separately. The three streams were replayed
again with backend order reversed. Every listed work counter repeated exactly
for each stream, including allocation and search statistics.

| Z3 statistic | Ferrum | Silicon owner + worker | Native increase |
| --- | ---: | ---: | ---: |
| Quantifier instantiations | 134,279 | 117,969 | 13.8% |
| Search decisions | 207,183 | Unavailable: owner omits statistic | Unavailable |
| Added equalities | 1,901,684 | 871,209 | 118.3% |
| Resource counter | 15,587,789 | 13,071,558 | 19.3% |

Source totals sum available counters from its two distinct solver processes.
The owner omits the decision statistic; the source worker reports 117,353.
The earlier combined-decision percentage assumed the omitted field was zero
and is withdrawn here. Missing statistics are unavailable. The quantifier,
added-equality and resource totals above are present in both streams and remain
supported. These are counters reported by this Z3 version, not timing or
allocated-memory sizes.
They describe a fixed captured path with active resource limits; they do not
recompute verifier decisions if a response were to differ.

Ferrum solver-only user+system CPU was 20.87 seconds initially and 8.49 seconds
in the reverse-order repeat. Silicon's two solver CPU totals were 5.63 and 7.41
seconds. The stable counters alongside variable timings rule out treating the
first apparent 3.7× solver CPU ratio as a stable result. Host/core/frequency
effects are possible explanations, but were not isolated here.

A separate offline history control omitted the 21 native function-phase
`check-sat` commands after the initial warmup while retaining other commands.
All 14,011 remaining responses matched. It reduced resource work from
15,587,789 to 15,265,497 (about 2.1%) and instantiations to 127,718. Simply
removing those checks did not eliminate the extra work. This altered fixed-trace
experiment is not a verified production optimization or a complete simulation
of source's fresh worker context.

## What this supports next

The count of checks and aggregate number of triggers do not explain the slow
tail. The next useful task is to minimize the late quantified-permission query
and its accumulated context, checking formula/trigger structure, assertion order,
symbol lifetimes and solver reuse until one controlled change explains the extra
work. The existing captures provide a reproducible input for that investigation.
No specific encoding defect, unsoundness or safe runtime optimization is claimed
from this comparison.

The [machine report](performance-nested-smt.json) retains query offsets, replies,
waits, option/budget audits, both repetitions, statistics, controls, sessions and
artifact hashes. [Compressed evidence](evidence/nested-smt/README.md) includes
complete command/response streams and chunk timestamps, plus the input and tool
hashes needed to audit them again. Full local artifacts, expanded analysis and
prover comments remain under `/tmp/ferrum-nested-smt-comparison`; structurally
corresponding-query review notes are under `/tmp/ferrum-nested-smt-review`.
