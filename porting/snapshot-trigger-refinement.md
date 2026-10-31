# Preserve heap-dependent snapshot triggers

After the allocation-order fix at `2e4578a`, Ferrum narrows the default
`--snapshotSummaryOnlyTriggers` optimization: resources used in heap-dependent
quantifier triggers keep both the summary-map and original-chunk lookup
alternatives. Other resources still use only the summary-map trigger. The
existing per-member resource-trigger analysis supplies this distinction;
configuration and resource membership remain fixed while summaries are cached.
No cache representation or solver-lifecycle default changes.

The quantified bodies, permission/domain guards, domain definitions and
resource-trigger definitions are unchanged. `--disableISCTriggers` still takes
precedence, and `--snapshotSummaryOnlyTriggers=false` restores both alternatives
everywhere. This repairs the observed trigger regression in the provable
linked-list configuration; it does not establish completeness for every input.

## Bounded comparison

Standalone runs use pinned upstream fixtures, Z3 from the existing Prusti
installation, one worker, branches off, a 30-second verification limit and a
65-second outer limit. Internal caches are disabled except where stated.
Concurrent correctness checks use disjoint CPU groups; elapsed times are not
treated as controlled performance measurements.

| Input/configuration | Observation |
| --- | --- |
| Linked-list append, separate method solver | Before refinement: `fold.failed:assertion.false` at line 60. After: verifies. |
| Append with `n.val := elem + 1`, separate solver | Correctly fails `postcondition.violated:assertion.false` at line 42. |
| Append, retained solver | Still times out at 30 seconds. |
| Append, separate solver, caches enabled | Both refined and original trigger policies time out. Both owner and worker SMT input/output prefixes are byte-identical between policies. |
| Graph marking, retained solver | Still times out at 30 seconds; no claim that its positive/negative obligations are resolved. |
| Quickselect, retained solver | Verifies before and after refinement with byte-identical complete SMT input/output. Its 43 snapshot-summary assertions have no resource-trigger definitions. |

The retained-solver append and graph cases previously returned incomplete
quantifiers under the broad summary-only policy. Replacing that rejection with
a timeout is not counted as a successful proof. Cache-enabled invalid append
also times out and is inconclusive. Timeout cancellation reports existing
worker cleanup warnings in the cache-enabled cases; the supervising process
reports no surviving descendants. These warnings remain in the evidence.

## Direct Prusti control

An isolated native server was rebuilt with the refinement and used for the
frozen `mut_element_nested_pass` Rust fixture, through cargo-prusti, VIR and the
native AST adapter. Internal caches are on, the outer result cache is off,
one worker is used, and branch parallelism is off. Verification/client/replay
limits are 60/100/45 seconds. The fixture/client checkpoint is the same
`a59ed917c1c3c4c4ca6ff1de12ad20d48491d021` snapshot used in the
[initial measurement](performance-summary-triggers.md); this is not a fresh
verification matrix of the live stdlib branch. That checkout was not changed.

The refined default's complete SMT input and output are byte-identical to the
earlier optimized direct-Prusti capture. All 136 snapshot-summary value axioms
remain optimized; there are no snapshot resource-trigger definitions on this
input. Its audited replay still takes **11,509 quantifier instantiations** and
**4,681,002 Z3 resource units**, preserving the original measured reduction.
A current-server run with the optimization disabled also verifies. Both replay
streams reproduce every captured response, with 1,111 checks each:

| Current-server policy | Quantifier instantiations | Z3 resource units |
| --- | ---: | ---: |
| Original lookup alternatives | 181,264 | 18,540,052 |
| Refined default | 11,509 | 4,681,002 |

The JSON records timings too; a single traced pair on a shared host is not a
new general speedup estimate.

## Checks and evidence

The expanded unit test covers protected/unprotected resources, domain guards
and `disableISCTriggers`, requiring identical bodies and non-value definitions.
All 309 enabled Silicon unit tests pass (43 external-solver tests are ignored).
The new real-Z3 integration regression runs valid append, invalid append and
valid append again in the same session under each trigger policy. All six
requests meet their expected outcomes. The imported CC0 fixture differs from
pinned Silver only in whitespace normalization.

Workspace/all-target checks pass with `native-z3`. Changed Rust files pass
rustfmt and the diff passes whitespace checks. The integration test can be run
with:

```sh
FERRUM_TEST_Z3=/path/to/z3 cargo +1.89.0 test --locked --offline \
  --test native_snapshot_summary_triggers -- --ignored --test-threads=1
```

[Machine-readable results](snapshot-trigger-refinement.json) bind binary,
source, fixture and trace hashes. The [evidence archive](evidence/snapshot-trigger-refinement/observations.tar.gz) includes the
patches, scripts, raw SMT streams, protocol audits, replay results and check
logs. It also retains excluded attempts: an invalid CPU affinity, a standalone
generated-Viper run killed by its outer limit before producing a verification
record, an initially overstrict multi-solver timeout audit, and a server build
retried with the required JVM library environment. None is counted as a proof
result or speed measurement.
