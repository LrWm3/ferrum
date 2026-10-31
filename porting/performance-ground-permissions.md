# Concrete permission-summary experiment

After selective snapshot triggers, permission-summary axioms became the main
quantifier hotspot in the profiled nested iterator case. A Z3 quantifier profile
recorded 7,145 of approximately 11,512 logged instantiations (62.1%) against
`qp.resPrmSumDef*` axioms. All 32 permission maps in that captured input were
used outside their definitions at concrete locations rather than inside other
quantified assertions. The profiler's logged total was three above Z3's final
global count, so the share is approximate.

The opt-in Ferrum flag `--groundPermissionSummaries` specializes eligible
permission-summary definitions at the current lookup arguments before assuming
them. The original quantified definition remains in the permission-map cache;
later lookups re-emit the relevant definition. The optimization defaults off.
It falls back to quantified definitions for trigger-dependent lookups, function
recording, quantified contexts, magic-wand packaging, old heaps, joins,
debugging, unsupported transformations, nested binders and other guarded
contexts. `--groundPermissionSummaries=false` explicitly selects the baseline.
The specialized axiom is an instance of the original axiom; using fewer
instances can still affect proof completeness.

In an offline screen, a transcript rewrite replaced 32 universal permission
definitions with 121 concrete instances in the nested case. It preserved all
14,032 recorded solver responses. In a mirrored baseline/candidate/candidate/
baseline replay, solver wall times were 2.628/2.636 seconds for the baseline and
1.915/1.922 seconds for the rewrite. Instantiations fell from 11,509 to 7,553,
while Z3 resource work fell from 4,681,002 to 4,588,324. These are diagnostic
replays, not direct-Prusti timings. The same rewrite preserved all responses on
a passing array case and its expected-failure control; their resource counts
fell from 569,924 to 527,920 and from 714,805 to 586,365, respectively.

The live verifier does not generate exactly that offline rewrite. On the nested
case, both modes successfully verified and all 1,111 solver check responses
matched. A relay audit found no protocol issues; replay reproduced each
capture's responses. The actual on/off inputs had 0 versus 32 quantified
permission-summary axioms. Z3 reported 9,412 versus 11,509 instantiations and
4,440,776 versus 4,681,002 resource units with the option on versus off.

The following untraced direct-Prusti timings use one fresh service per request,
one worker, branch parallelism off, internal caches on, outer result cache off,
and CPU affinity 0–3 for server and solver. They use the frozen Prusti source
`13cfa41842e4f1956cd0dffbfa414b24aa8049f5`, PCG `c18a5189`, and Ferrum
`a82fe32` plus the experimental patch. The 60-second verifier and 100-second
client limits, input bytes and dependency seeds were the same in both modes.
The nested case used off/on/on/off order; the two other two-pair cases were
repeated in the opposite order after the initial sample. Each observation is
retained. A Rust test build overlapped the early measurements on CPUs 4–11,
and the shared host and small sample make fine-grained latency claims uncertain.
The third `mut_native_empty_pass` pair used the final build described below.

| Fixture | Expected result | Off, seconds | On, seconds |
| --- | --- | --- | --- |
| `mut_element_nested_pass` | Verified | 8.71, 7.83 | 8.25, 8.09 |
| `mut_native_empty_pass` | Verified | 10.52, 11.72, 11.55 | 8.07, 9.24, 10.12 |
| `mut_native_restoration_vec_wrong` | Expected failure | 18.33, 11.68 | 24.33, 17.62 |
| `collection_get_mut_expiry_pass` | Verified | 9.01 | 7.51 |
| `shared_into_iter_wrong_value` | Expected failure | 0.93 | 0.88 |
| `symbolic_pass` | Verified | 12.54 | 13.27 |

All of these cases retained their expected outcome, including both negative
controls. The first two observations of `mut_native_empty_pass` show a roughly
22% lower median request time; the final-build pair improved by 12%. The nested
observations are close despite lower solver
work, and the single-observation cases do not establish reliable speedups.
The restoration failure ran slower with the option in both pairs. Follow-up
traces for that case had byte-identical solver inputs and outputs, with no
permission-summary axioms in either mode. Thus the observed timing variation
does not reflect a change in the solver workload for that capture; host and
frontend timing remain potential contributors.

The final build was adjusted after these measurements to avoid copying the
definition vector when the experimental flag is disabled. A final nested
trace with the final build had byte-identical off/on SMT inputs and outputs to
the corresponding measured-build traces. It verified successfully in both
modes. All 308 enabled Silicon unit tests passed (43 opt-in tests ignored).
The tests cover option wiring, substitution of multiple arguments, fallback on
invalid arity and sorts, non-quantified definitions, nested binders and context
guards. The workspace check is recorded separately in the commit validation.

A separate bounded sweep changed Z3's quantifier eager threshold from the
current 1,000 to 10, 100, 500, 2,000 and 5,000 on the nested capture. Each
completed with identical responses, 11,509 instantiations and 4,681,002 resource
units. It supplied no evidence for changing that setting.

The [machine-readable evidence](performance-ground-permissions.json) records
the per-request outcomes, phase and CPU data, solver replay statistics, trace
audits, frozen server hashes and the experimental patch. Raw captures and
scripts are in `/tmp/ferrum-next-solver-work`. This is a focused experiment,
not a full stdlib compatibility matrix, and the active stdlib worktree was not
modified. Its pinned Ferrum revision must be updated separately to use this
revision.
