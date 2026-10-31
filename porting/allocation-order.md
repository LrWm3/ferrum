# Deterministic allocation assumptions

`compute_reference_disjointnesses` now uses insertion-ordered sets for references,
sets of references and sequences of references. It retains first occurrence in
the existing ordered store/heap traversal, preserves the three resource groups,
deduplicates equal terms, and excludes the new reference itself. Formulas and
permissions are unchanged. This replaces Rust's randomized hash-table emission
order; it does not reproduce Scala's incidental HashSet ordering.

The preceding [timeout investigation](timeout-followup.md) found identical runs
diverging at their 1,680th SMT command, during allocation. With this fix, three
fresh runs of the original linked-list-with-wands fixture have byte-identical
complete captured input and output prefixes:

- 3,547 commands and 331 solver checks in each run.
- Input SHA-256: `60e72ea7287bc9c1ad39a5dc9853d76d5829d409e2865a5b67e3a0e40e5f0b60`.
- Output SHA-256: `3fe30b548f860dffbffaab64ffa8f51878a6bca704bdd4f63c15f64926cb6dce`.
- All three reach the 30-second verifier timeout at the same unanswered final
  check. This fixes reproducibility, not that proof's timeout.

Positive allocation controls prove distinct fresh objects and exclusion from
existing reference sets/sequences. The negative control rejects equality with
an existing object at its intended assertion. All five captures pass protocol
and supervisor-cleanup checks, allowing only the final unanswered query in the
three timeout prefixes. They use one worker, branch parallelism off and disabled
internal caches, with the existing Z3 and development build profile. Concurrent
runs use disjoint CPU sets on the shared host; no speedup is claimed.

The regression unit test checks exact stable grouping/order, duplicate references
across store and heap, collection membership, irrelevant sorts, and exclusion of
the new reference across 128 fresh collections. All 309 enabled Silicon unit
tests pass, with 43 opt-in tests ignored. The compatibility example
build and changed-file formatting check pass. The first test compilation exposed
an incorrect test-only Box/Arc constructor and is preserved alongside the fixed
build logs.

[Machine evidence](allocation-order.json) binds the patch, frozen source hashes,
binary, commands and all outcomes. The
[evidence archive](evidence/allocation-order/observations.tar.gz) preserves raw
streams, results, controls, runner and build/test logs. Working artifacts are
under `/tmp/ferrum-order-trigger-fix`. This chunk does not change trigger policy;
the append completeness issue is handled separately.
