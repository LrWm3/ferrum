# Stdlib follow-up review (2026-10-31)

The completed paired portions of the stdlib agent's `final339` matrix contain
three Ferrum-only failures: `vec_lookup_range_pass`, `mut_element_replace_pass`,
and `mut_element_replace_return_pass`. All three verify in fresh requests using
the checkpoint349 native adapter pinned to Ferrum `85fc9d8`. The full matrix
still uses the older `afdf10c` backend; its failures do not establish regressions
on current Ferrum.

## Fresh Prusti checks

The isolated source is a copy of `/tmp/prusti-stdlib-probe349`, based on Prusti
`d2678d5c0` with the dependency-only Ferrum upgrade. Each check uses a fresh
server, one worker, branch parallelism disabled, verification-result caching
disabled, and internal caches enabled. Bounds are 180 seconds per program for
the range cases, 60 seconds for replacement cases, 30 seconds per assertion,
and 100 milliseconds per check with prover time bounds enabled.

| Rust case | Result |
| --- | --- |
| `vec_lookup_range_pass` | Full verification succeeds, including generated helpers |
| `inclusive_wrong_frame` | Only the expected assertion at line 11, in two fresh runs |
| `mut_element_replace_pass` | Full verification succeeds |
| `mut_element_replace_return_pass` | Full verification succeeds |
| `mut_element_replace_false` | Only the expected assertion at line 6 |

Both inclusive-frame runs emit the exact Viper bytes from the agent's unstable
build336/build337 comparison: SHA-256
`740d218632baf3df90ef60e309c2a6cb38197164b4eab70c4ac5800943ee045f`.
The fresh range-positive dump differs from `final339` only in comments and
generated 32-digit macro identifiers. These targeted checks support using the
existing permission fix; they do not establish universal solver stability or
replace the stdlib agent's full upgrade qualification.

These are correctness checks, not qualified performance comparisons. The
isolated source path invalidated the copied dependency build cache, so the
benchmark runner's strict dependency-event check fails even though each actual
verification result is correct. Dependency verification remained disabled;
Prusti support crates and the spec library were rebuilt. All owned client,
server, and solver processes were cleaned up. The companion JSON retains these
limitations and the actual exit codes rather than treating the runner's exit
status as a proof result.

## Viper replay repairs

Replaying the original Viper dumps exposed two frontend performance defects.
They affect parsing and checking Viper text. Prusti's injected-AST adapter
bypasses these operations, so these repairs are not evidence of faster Rust
verification through that adapter.

1. ADT field and discriminator inference checked the receiver to select its
   signature, then checked it again while applying that signature. Nested field
   accesses doubled the work at each level. `09a28fb` reuses the receiver's
   inferred type and substitution candidates. The regression observes 1,536
   resolutions of the leaf call on the old implementation and a constant bound
   with the fix. Generic field selection, colliding field names, discriminator
   result types, and incompatible contexts remain checked.
2. Grounding an expression copied the entire solved type-substitution map into
   every descendant. A diagnostic replay with only the first fix reached about
   18 GiB of resident memory and was stopped after 191 seconds, still before
   verification queries. Substitutions now share their immutable mappings;
   generalisation copies before mutation and other modifying operations still
   return independent maps. This follows the immutable-map ownership of
   Silver's `PTypeSubstitution`, without changing its constraints or defaults.
   This repair is `0e048a4`.

The initial unfixed replay exhausted a 125-second outer limit without emitting
verification queries. Those incomplete runs are frontend diagnostics, not
solver timeouts or proof failures. The retained profiles identify repeated
receiver checks first, then map cloning during `force_substitution`.

With both repairs, the original range-positive Viper file verifies in 99.75
seconds; maximum process-tree RSS is 1.28 GiB. The original inclusive negative
finishes in 151.83 seconds with only `exhale.failed:assertion.false` at Viper
line 4202, the encoding of `values[2] == 9`. Neither replay reports an
aggregate-helper failure. Both include all methods and functions and pass
solver-trace and process-cleanup checks. Their frontend overhead and concurrent
build activity make their wall times unsuitable for comparison with the
injected-AST Rust runs.

All 438 Silver library tests, the ADT regression, two substitution-independence
tests, and `cargo check --workspace` pass. Eighteen upstream ADT files preserve
the complete native result records before/after both repairs. Their outcomes,
37 expected error IDs, and source positions also match pinned Silicon. One
pre-existing message line-wrapping difference remains in `destructors_5.vpr`.

## Other findings

The proposed delayed-owner-handoff models are rejected by both current Ferrum
and pinned Silicon because a local named `current` duplicates a let-bound name.
That model must first pass the shared frontend rules before it can establish a
backend permission discrepancy.

The optional-tail conversion, nested owned collections, and generic owner
handoff findings remain Prusti encoder/PCG work or require a completed paired
comparison. The large inclusive positive times out on both backends. This
review does not repair those paths or classify them as Ferrum-only failures.

Raw artifacts are under `/tmp/ferrum-stdlib-followup-ba666a7`. The companion
`stdlib-followup-review.json` records hashes and selected results. No source
files or backend pin in the active Prusti working tree were changed.
