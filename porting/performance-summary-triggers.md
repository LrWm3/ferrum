# Selective snapshot-summary triggers in direct Prusti verification

Ferrum `783bd7e` adds the opt-in `--snapshotSummaryOnlyTriggers` policy. On the
frozen nested mutable-iterator case, it reduces Z3 resource work by **74.75%**
and quantifier instantiations by **93.65%**, while preserving every original
solver response. Two short untraced observations per configuration show the
request falling from 13.01/16.09 seconds to 5.34/6.76 seconds: **2.40 times faster
using the two-observation medians**. This is a substantial improvement on this
case, not a performance claim for the full stdlib matrix.

The earlier quantifier profile attributed about 65.5% of logged instantiations
to `qp.psmValDef*` snapshot-summary value axioms. Each originally had alternative
triggers on the summary-map lookup and the original chunk-map lookup. Looking
up an old chunk could therefore activate many summaries. The new policy keeps
only the summary-map lookup trigger, so those axioms activate when the summary
is used. The quantified formulas, permission/domain guards, domain axioms and
resource-trigger axioms are unchanged. This deliberately differs from the
pinned Silicon trigger policy; it is not a correction of a porting mismatch.

At the time of these measurements the option defaulted to false. It has since
been enabled by default; `--snapshotSummaryOnlyTriggers=false` restores the
previous trigger policy, and `--disableISCTriggers` takes precedence.
Trigger selection can affect whether a proof succeeds within its limits even
with unchanged formulas. The bounded passing/failing checks below justify
trying the option on more workloads; they do not establish compatibility with
the full stdlib matrix.

The runs use actual Rust input through `cargo-prusti`, VIR and the native
VIR-to-Silver AST adapter. Prusti source/client/adapter and fixtures are frozen
at `a59ed917c1c3c4c4ca6ff1de12ad20d48491d021`, with PCG
`c18a51899e37e0fa67f9b5f17f7d518ef2f5518c`. These are **not** new runs of the
latest stdlib branch. The active stdlib checkout was not edited. Server builds
use the isolated source at `/tmp/ferrum-direct-profile-49d3737/source`,
`nightly-2026-08-15`, and the development profile with the Ferrum packages at
optimization level 1. All four timing profiles use the same frozen production
server. The initial nested separate-solver capture reused the preserved
`4cda819` server, before the trigger implementation was built. All other
correctness captures use `783bd7e`, when the new trigger option defaulted off.

Controls are one worker, branch parallelism off, internal caches on, Prusti's
outer result cache off, the existing resource-bound policy and saturation
weights `[1, 0.5, 0.4, 0, 0]`. Server/solver affinity is CPUs 0–3. Each trial uses
a fresh service and a disposable dependency seed; only the root Rust fixture
is checked. Limits are 60 seconds for verification, 100 seconds for the client
and 45 seconds for offline replay. No old saturation profile is mixed in.

The first screen edited only the second trigger of 136 `qp.psmValDef*` axioms in
an existing direct-Prusti transcript. It preserved all 14,032 original protocol
responses. The implementation's direct-Prusti output then matched that screen:
its SMT input is equivalent after whitespace normalization and its complete
response stream is byte-identical to the default stream. The default profile's
input remains byte-identical to the preceding `4cda819` runtime.

The following counts come from audited captures and bounded replays. Each
replay reproduced its entire captured response prefix without protocol gaps.
Separate/combined totals include **both** owner and worker solver streams.
The separate option lets methods share a worker solver, while functions and
predicates use the owner solver; it does not create a new solver for every method.

| Nested fixture profile | SMT checks | Quantifier instantiations | Z3 resource units | Change in resource units |
| --- | ---: | ---: | ---: | ---: |
| Default | 1,111 | 181,264 | 18,540,052 | — |
| Summary trigger only | 1,111 | 11,509 | 4,681,002 | −74.75% |
| Separate method solver only | 1,112 | 137,899 | 14,890,364 | −19.69% |
| Both options | 1,112 | 11,096 | 4,838,599 | −73.90% |

The small array controls show why the options should remain independent:

| Array fixture / profile | Quantifier instantiations | Z3 resource units | Change in resource units |
| --- | ---: | ---: | ---: |
| Passing / default | 1,337 | 613,017 | — |
| Passing / summary trigger | 867 | 569,924 | −7.03% |
| Passing / separate solver | 1,280 | 819,033 | +33.61% |
| Passing / both | 870 | 777,676 | +26.86% |
| Expected failure / default | 1,609 | 774,833 | — |
| Expected failure / summary trigger | 1,012 | 714,805 | −7.75% |
| Expected failure / separate solver | 1,612 | 982,583 | +26.81% |
| Expected failure / both | 1,015 | 922,557 | +19.07% |

After all builds, diagnostic captures and replay audits completed, 16 untraced
timing trials ran sequentially. For each positive fixture, the profile order
was default, trigger, separate, both, both, separate, trigger, default. Every
observation is retained, with no performance-result retries. The request timer
excludes service startup but includes the Rust client invocation. Backend time
includes solver time. Native CPU is the server's user plus system time; solver
CPU is its reaped child CPU time. Neither profiling nor the SMT relay is active
in this block.

| Nested profile | Request seconds, both observations | Median backend seconds | Median solver CPU seconds | Median native CPU seconds |
| --- | --- | ---: | ---: | ---: |
| Default | 13.01, 16.09 | 13.486 | 11.735 | 2.070 |
| Summary trigger | 5.34, 6.76 | 4.973 | 3.265 | 2.040 |
| Separate solver | 9.61, 14.53 | 10.773 | 8.915 | 2.260 |
| Both | 5.11, 5.19 | 4.161 | 2.705 | 1.775 |

The trigger-only backend median falls by 63.12%, with essentially unchanged
native CPU. The gain comes from reduced solver work. Both options produced the
lowest times in this small block, but consumed 3.37% more solver resources than
the trigger option alone. With two observations and substantial shared-host
variation, this does not establish an additional benefit from combining them.

Array request observations were 1.80/1.28 seconds by default, 1.63/1.30 with the
trigger option, 1.78/1.34 with the separate solver, and 1.65/1.41 with both.
The differences are small relative to the variation. The resource counters
support a modest trigger improvement and a separate-solver regression here;
the timing block does not establish a small-case latency improvement.

There are 22 valid correctness observations across eight Rust fixtures. All
four configurations were checked on the first three; default and trigger-only
were checked on the other five. Failure locations remained compatible.

| Rust fixture | Expected result |
| --- | --- |
| `mut_element_nested_pass` | Verified |
| `mut_element_array_pass` | Verified |
| `mut_element_array_wrong` | Assertion failure, line 8 |
| `mut_element_nested_frame_wrong` | Assertion failure, line 11 |
| `mut_element_option_pass` | Verified |
| `mut_element_pair_merged_pass` | Verified |
| `mut_element_replace_false` | Assertion failure, line 6 |
| `mut_native_shared_ref_next_wrong` | Assertion failure, line 8, column 28 |

All 305 enabled Silicon unit tests passed (43 opt-in tests ignored), and
`cargo +1.89.0 check --workspace --all-targets --features native-z3` passed.
New tests check CLI/default wiring and that the trigger policy preserves
quantified bodies, conditional permissions, domains, resource triggers and
the precedence of `disableISCTriggers`. The unit-test build preceded removal
of an unused `mut` in test code; the final workspace check covered that cleanup.
Every valid trial completed without timeout or dependency rebuild, and its
cleanup audit found no remaining owned descendants.

Two harness mistakes are retained explicitly in the evidence. Five initial
default trials passed a trailing blank option and failed with “Too many file
arguments”; these were setup failures, not performance observations. Only
those five were repeated after stripping the blank, under `-fixed` names.
The shared-reference negative test initially expected source line 9, but source
inspection shows the assertion on line 8. Both original default/trigger runs
failed correctly at line 8, column 28. Their original `unexpected_result`
records remain intact; derived evidence records the corrected oracle without
rerunning them. The first offline screen also had a Python bytes/string
preflight error before starting Z3; its error log is retained separately.

The snapshot-reuse investigation found 136 distinct value axioms for 32 maps,
with no exact repeated assertions to remove. The maps form 16 pairs with
matching complete value-definition bodies after renaming only the summary map
and bound variable. The earlier definitions are still in an ancestor or equal
solver scope when the later definitions appear.

A separate diagnostic build logged cache accesses without changing behavior;
its entire SMT input and output match the default capture. It recorded 73
lookups, 27 exact key/domain hits and 46 insertions. In **all 16 matching pairs**,
the earlier map was absent from the current state's cache when the new map was
created. No candidate in the existing cache failed solely because of the
compared metadata fields. Merely relaxing key equality cannot fix these pairs.
The cache histories point toward restoration of older state snapshots, but the
precise state-transition cause has not yet been isolated.

No cache-reuse change was shipped. A sound follow-up must establish compatible
permission totals, domains, function/quantifier context and solver scope before
carrying summaries across restored states. Equal value axioms alone are
insufficient: they test positive permission while the cached total records the
actual amount. The diagnostic source patch was removed after capturing the
evidence; its patch and frozen binary remain in the raw artifact directory.

[Machine-readable evidence](performance-summary-triggers.json) preserves the
complete timing schedule and observations, correctness classifications and
corrections, all-stream solver audits, cache pairs, artifact hashes and build
context. Raw artifacts are in `/tmp/ferrum-solver-work-0e1bf91`. The production
binary is `trigger-server`; `cache-diagnostic-server` is diagnostic only.
The earlier quantifier profile is in
`/tmp/ferrum-solver-quantifier-focus-4cda819`; its logged instantiation total was
three above Z3's final global count, so the motivating 65.5% share is approximate.

The raw directory contains `screen_trigger.py`, `run_direct.py`,
`validate.py`, `audit_trial.py`, `time_profiles.py`, `analyze_summaries.py`,
`summary_contexts.py` and `collect_evidence.py`. For example, a new bounded
direct trial using the prepared frozen inputs is:

```sh
python3 /tmp/ferrum-solver-work-0e1bf91/run_direct.py new-trigger-trial \
  --server /tmp/ferrum-solver-work-0e1bf91/trigger-server \
  --case mut_element_nested_pass --options=--snapshotSummaryOnlyTriggers
```

Use a new output name. Add `--trace` for protocol auditing and replay; keep it
off for timing. Other configurations are the empty option string,
`--separateMethodSolver`, or both flags. The evidence records the frozen source,
binary, client, solver and harness identities. Rebuilding the isolated server
uses the same locked native command documented in
[the preceding direct profile](performance-path-conditions.md).
