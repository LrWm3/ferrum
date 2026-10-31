# Stdlib permission failure review (2026-10-31)

The two reported mutable-reference replacement positives are repaired:
`mut_element_replace_pass` and `mut_element_replace_return_pass` now verify
through Prusti's native Ferrum adapter. Their false-assertion control still
reports `assert.failed:assertion.false` at Rust line 6.

Runtime fix: `85fc9d8` (`silicon: Preserve wand permission-map definitions`).

## Cause and repair

Wand packaging retains definitions independent of its hypothetical left-hand
heap, but keeps assumptions about that heap behind the wand token. The residual
outer heap can contain permissions guarded by `perm(...)` branch conditions.
Those conditions need their permission-map definitions after packaging ends.

Two details prevented that:

1. Permission-summary equations were recorded as ordinary assumptions. They
   disappeared when the package scope closed. Record permission-map equations
   as definitions, on cache hits as well as misses and with debugging enabled
   as well as disabled. Snapshot-value equations retain their existing policy.
2. Permission-removal macros always took every surrounding wand snapshot as an
   argument, even when their bodies did not use it. The package dependency check
   consequently discarded otherwise independent definitions that mentioned
   those macros. Omit unused additional parameters; retain any parameter whose
   occurrence cannot be determined. Macro bodies and consumed amounts are
   unchanged. Codomain parameters retain their original order.

The package's token guard and snapshot-dependency filter are unchanged. No
left-hand-side assumptions, permission checks, or injectivity checks are
weakened. A definition that actually uses the hypothetical snapshot remains
subject to the existing filter.

`wand_permission_branch.vpr` isolates the first defect. The macro variant
exhales a conditional half permission before branching and requires both fixes.
The nested variant checks propagation through an enclosing package. Regression
coverage also rejects consumed permissions, an escaped LHS boolean assumption,
and an unjustified frame depending on an unknown LHS field value. It reuses a
verification session after failures and runs with caches both enabled and
disabled. Debug definition classification is checked in the existing metadata
unit test; full quantified-wand execution with debugging still has an unrelated
unsupported transfer path.

## Evidence

Raw local artifacts are under `/tmp/ferrum-stdlib-review-b8f76d8`; parsed Viper
replays are under `/tmp/ferrum-order-trigger-fix/stdlib-*`. The companion JSON
records selected results and artifact hashes. These are verification checks,
not controlled performance measurements.

| Fresh Prusti input | Before | Fixed backend time | Fixed result |
| --- | --- | ---: | --- |
| `mut_element_replace_return_pass` | Insufficient permission in implicit postcondition | 0.90 s | Verified |
| `mut_element_replace_pass` | Insufficient permission in implicit postcondition | 2.71 s | Verified |
| `mut_element_replace_false` | Expected false assertion | 0.52 s | Expected assertion at line 6 |

The isolated client is checkpoint255; fixtures and the native adapter come from
`/tmp/ferrum-trigger-sample-13cfa/source`. Both positive Rust inputs have the same
hashes as the failing runs. No files or backend pin in the active stdlib working
tree were changed. Each run uses a fresh request, includes generated helpers,
and checks process-tree cleanup and dependency verification status.

The return-case Viper dump also fails on pinned Scala Silicon `ff386aec` and
passes on Prusti's bundled Silicon `6b540aa4`. Thus this was not solely a Rust
translation error. The patch repairs an inherited completeness problem while
preserving the newer token-based package model. Turning off summary-only
triggers, disabling caches, or separating method solvers did not repair it.

`cargo check --workspace`, the new regression test, the debug-metadata test,
and seven existing native CLI wand tests passed.

A seven-input upstream wand comparison retains identical outcomes, error IDs,
and source positions before/after this fix and against pinned Silicon. It
covers conditional footprints, `perm`, quantified fields and predicates,
repeated wand application, and nested snapshots: one successful input and
27 expected diagnostics across the other six inputs.

## Previously deferred prefix qualification

The checkpoint255 report on Ferrum `2df948c` failed the heavy
`mut_native_resource_pair_prefix_wrong_second` at loop restoration instead of
its expected final assertion. That earlier failure did not reproduce on
`b8f76d8`: the full positive verified, and the full negative reached its expected
assertion at line 44. The same negative also reached line 44 with the original
snapshot-trigger policy. These runs used one worker, branch parallelism off,
600 s program / 30 s assertion / 100 ms check time bounds.

The same full pair also passed on the final wand fix (`85fc9d8`): the
positive verified in 229.10 s of backend time and the negative reported the
expected line-44 assertion in 308.71 s. Request wall times were 246.06 s and
336.51 s. Both used the same time bounds and passed cleanup checks. These were
concurrent qualification checks with other compilation activity, so the timings
are not a before/after speed comparison.

An additional experiment retained both trigger directions for parameterized
snapshot maps. It did not repair a failing proof or demonstrate an advantage
over the existing trigger guard and was reverted. This patch does not change
the trigger policy or its default.

This targeted evidence does not replace the stdlib project's full backend
upgrade qualification matrix.
