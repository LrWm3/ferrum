# Snapshot trigger sample on current Prusti

On a frozen sample of Prusti `13cfa4184`, **23 of 27 cases produced their
expected result with the trigger option both off and on**. Two positive cases
failed identically in both modes; two recent iterator-prefix cases timed out in
both modes. No on/off outcome difference was observed. The timeouts and shared
failures limit what this sample can establish about broader compatibility.

The 23 expected-result pairs took a total of **89.68 seconds off and 80.22
seconds on** for the timed client requests, a 10.5% reduction in this sample.
The nested mutable iterator accounted for 7.38 of the 9.46 seconds saved:
12.61 seconds off versus 5.23 on. Without that case, the other 22 totaled 77.07
versus 74.99 seconds. Each case was run once per setting on a shared host, so
these totals are a useful screen, not a stable estimate of a full-matrix speedup.

The sample has 27 cases across nine suites, selected before either mode ran.
For each suite a seeded random sample chose a positive case and an expected
verification failure; iterator has three of each, borrow two of each, and
three iterator cases were added deliberately: the previously profiled nested
case and two recent two-reference prefix cases. Seed `20261030` also shuffled
the case order; the first configuration alternated between off and on. Of the
23 cases with expected outcomes, 11 were successful proofs and 12 returned
their expected verification failures and locations. All 23 had a backend
verification phase in each mode.

Prusti and PCG were archived from commits
`13cfa41842e4f1956cd0dffbfa414b24aa8049f5` and
`c18a51899e37e0fa67f9b5f17f7d518ef2f5518c`, respectively. The archive was
taken before concurrent, uncommitted stdlib changes that appeared during the
run, so it does not include those later edits. In the isolated copy only,
`prusti-ferrum` and its lockfile were switched from the branch's pinned Ferrum
revision to local Ferrum `a2e7b609877326c623bc0854a989c9f2eaa700d6`, including
trigger change `783bd7e`. The active stdlib worktree was not edited.

Both modes used the same newly built Prusti client and native server, the same
Z3 4.16.0 and fixtures, one worker, branch parallelism off, internal caches on
and Prusti's outer result cache off. Each observation used a fresh service and
a disposable copy of its suite's prebuilt dependency target. Only the selected
client package was rechecked; the spec libraries were not separately verified
in this sample. Server and solver affinity was CPUs 0–3. The normal verifier
limit was 60 seconds with a 100-second outer limit. The iterator-resource
suite used 180/220 seconds, 30-second per-check/assert limits and time bounds,
matching that suite's special configuration. The 60-second limit is shorter
than the stdlib harness's normal 180-second default.

Untraced request times are shown below. A timeout is censored: the listed
elapsed time includes time spent reaching the limit and is not a completed
verification duration. Service startup is excluded from all these times.

| Suite | Case | Outcome in both modes | Off, s | On, s |
| --- | --- | --- | ---: | ---: |
| `borrow` | `ghost_snapshot_loop_pass` | Expected | 1.01 | 1.07 |
| `borrow` | `ghost_snapshot_reassigned_wrong` | Expected | 1.33 | 1.11 |
| `borrow` | `quantified_expiry_heap_pass` | Expected | 0.71 | 0.68 |
| `borrow` | `range_wrong_frame` | Expected | 9.22 | 8.74 |
| `collections` | `slices_pass` | Same unexpected failure | 17.42 | 14.59 |
| `collections` | `swap_remove_stable_order` | Expected | 1.11 | 1.10 |
| `extern` | `conditional_pre_wrong` | Expected | 0.75 | 0.56 |
| `extern` | `pass` | Same unexpected failure | 2.02 | 2.15 |
| `hash` | `collection_clear_unbound` | Expected | 1.96 | 2.02 |
| `hash` | `collection_get_mut_expiry_pass` | Expected | 11.06 | 12.58 |
| `iterator` | `mut_element_nested_pass` | Expected | 12.61 | 5.23 |
| `iterator` | `mut_element_prefix_pass` | Expected | 3.22 | 3.00 |
| `iterator` | `mut_expiry_selector_nested_wrong` | Expected | 0.68 | 0.64 |
| `iterator` | `mut_generic_pair_pass` | Expected | 1.25 | 1.35 |
| `iterator` | `mut_native_empty_pass` | Expected | 11.40 | 7.17 |
| `iterator` | `mut_native_resource_pair_prefix_pass` | Both timed out | 72.88 | 70.74 |
| `iterator` | `mut_native_resource_pair_prefix_wrong_second` | Both timed out | 71.47 | 68.65 |
| `iterator` | `mut_native_restoration_vec_wrong` | Expected | 17.17 | 19.26 |
| `iterator` | `shared_into_iter_wrong_value` | Expected | 1.23 | 1.20 |
| `iterator_resources` | `native_resource_cross_false` | Expected | 1.06 | 1.14 |
| `iterator_resources` | `native_resource_cross_pass` | Expected | 1.25 | 1.13 |
| `resources` | `associated_wrong` | Expected | 1.16 | 1.05 |
| `resources` | `expiry_selector_pass` | Expected | 0.74 | 0.76 |
| `sequence` | `triggers_pass` | Expected | 0.84 | 0.84 |
| `sequence` | `wrong_element` | Expected | 0.57 | 0.64 |
| `vec` | `length_overflow` | Expected | 0.75 | 0.78 |
| `vec` | `symbolic_pass` | Expected | 8.60 | 8.17 |

For the 23 expected-result pairs, summed backend time was 61.545 seconds off
and 49.231 on. The median per-case off/on request-time ratio was 1.025; 13
cases were faster on, nine slower and one tied to the timer's 0.01-second
resolution. Small differences are susceptible to shared-host noise. No
separate method solver or branch-parallelism experiment is mixed in.

The shared unexpected failures were:

- `extern/pass`: both modes reported a Prusti internal error after Ferrum
  returned a postcondition/insufficient-permission error without a source
  position for `m_replace_generic`.
- `collections/slices_pass`: both modes reported insufficient permission to
  call `values.swap(a, b)` at `slices_pass.rs:76:5`.

`mut_native_resource_pair_prefix_pass` and
`mut_native_resource_pair_prefix_wrong_second` both reached the 60-second
verifier limit in both modes, so neither establishes its expected result. The
first pair was run by an earlier harness version that classified Prusti's
lowercase “verification timed out” diagnostic as `unexpected_result`. Its
original records are preserved; the derived analysis corrects both to
`censored_timeout`. The harness was corrected before the remaining pairs. No
timing result was retried or discarded.

An additional, untimed trace pair for `mut_element_nested_pass` confirmed the
option was effective on this build. Both proofs succeeded, their complete
solver responses were byte-identical, and each had 1,111 solver checks with no
protocol issues. The on and off inputs match byte-for-byte the respective
inputs in [the previous trigger study](performance-summary-triggers.md), whose
bounded replays measured 18,540,052 versus 4,681,002 Z3 resource units. The
trace runs are excluded from the table and timing totals above.

All 51 postflight checks passed for the frozen client/server binaries, solver,
fixture locks, copied dependency seeds, selected source files and sample
manifest. Each trial's owned client and service cleanup audit passed. The
[machine-readable evidence](performance-trigger-stdlib-sample.json) contains
case selection, execution order, raw and reviewed classifications, timings,
diagnostics, phase and cleanup data, binary and log hashes, and trace audit.
Raw logs and the isolated preparation/runner scripts are under
`/tmp/ferrum-trigger-sample-13cfa`.

This sample supports trying the option on the stdlib branch, but is not yet a
reason to change Ferrum's global default: the two prefix cases need a longer
paired run, the shared failures need baseline investigation, and the rest of
the stdlib matrix remains untested with this option.
