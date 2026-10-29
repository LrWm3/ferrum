# Fresh Prusti validation checkpoint

The full matrix is **in progress**. This records the frozen inputs, completed
builds and individually reproduced findings; it is not a completed matrix or a
performance comparison. Historical eight-case results are not reused.

## Source and builds

Integration commit `13674e5e2e46eff8f6140bece1a988e0db22893e` on
`codex/stage3-verification` in `LrWm3/prusti-stdlib` combines committed stdlib
snapshot `708b0063c1ebc76521e89291d4fab16e3b63bcc3` and native adapter
`1b994e3895816c92c6aa793d4540fca829dd9635`. Ferrum is pinned to
`f686fde563e0e971d20a46eb8dd14e083a11e801`, and pcg to
`c18a51899e37e0fa67f9b5f17f7d518ef2f5518c`. The separate integration checkout
preserves the user's active stdlib checkout and its uncommitted changes.

Both locked builds passed with nightly-2026-08-15:

```
cargo build --locked -p prusti --no-default-features --features ferrum
cargo build --locked -p prusti --features ferrum
```

The JVM configuration uses JDK 17 and its `lib/server` library path. Separate
target directories keep the native-only and dual builds independent; each also
builds `prusti-launch` for `cargo-prusti`.

| Artifact | SHA-256 |
| --- | --- |
| Native-only `prusti-driver` | `ce511b3181e5d66a60b5a699491211d7f3ac241c53d844a310d6d4a4f5da16c3` |
| Dual `prusti-driver` | `116a67851ad7b4a69cff1886a45ab1f4f2377ababc2458854c4de79dde1a31a7` |
| Bundled `viperserver.jar` (Silicon `6b540aa4`) | `6d11d2b73efe97b97026050f13d966c5ec599cf70d43022346382e065a49cf7c` |
| Standalone pinned Silicon `ff386aec` jar | `bcab94591994788e41a62fa673f1001339ac2323ef58e27d428a7ca739c12726` |
| Z3 executable, 4.16 | `e583c4186a45e72411fa2cb2048401eed03f0f8e5f24694676a8f6271a50b765` |

The bundled Silicon is older (2026-08-27) than Ferrum's pinned source
(2026-10-20). The fresh Rust matrix exercises the actual Prusti bundle; targeted
replays and the subsequent broader compatibility stage distinguish these two
reference versions.

## Matrix scope and settings

| Suite | Positive clients | Negative clients | Total |
| --- | ---: | ---: | ---: |
| iterator | 116 | 194 | 310 |
| borrow | 51 | 58 | 109 |
| extern | 15 | 63 | 78 |
| hash | 9 | 31 | 40 |
| collections | 3 | 19 | 22 |
| sequence | 3 | 12 | 15 |
| vec | 5 | 9 | 14 |
| resources | 7 | 7 | 14 |
| Total | 209 | 393 | 602 |

Each backend runs all client binaries plus spec-library, Rust compilation and
positive runtime controls. Extern core-only and sequence trigger checks remain
separate controls. A runtime success is not counted as a verified client.
Standalone `known_limits` probes are outside this client inventory.

Each suite uses the frozen integration harness:

```
python3 scripts/test_stdlib_extern_spec.py --backend Ferrum --suite iterator --log-dir RESULTS/native/iterator
python3 scripts/test_stdlib_extern_spec.py --backend Silicon --suite iterator --log-dir RESULTS/jvm/iterator
```

Select the appropriate build with `CARGO_TARGET_DIR`, and repeat for each suite.
The harness clears inherited `PRUSTI_*` options before explicitly setting its
backend. It disables Prusti's verification cache and dependency verification,
enables overflow and panic checks, and uses fresh Cargo verification targets.
The backend's internal caches retain their defaults. Effective backend options
include the following, with the configured Z3 executable:

```
--timeout 180 --numberOfParallelVerifiers 1 --numberOfErrorsToReport 1
--enableMoreCompleteExhale --disableTerminationPlugin --assertTimeout 10000
--proverConfigArgs "smt.qi.eager_threshold=1000 model.partial=false smt.arith.solver=6"
--logLevel ERROR
```

The default solver assertion setting is distinct from the 180-second program
deadline; `--proverEnableTimeBounds` is not enabled. The external command bound
is 300 seconds. Harness timeouts, verifier timeouts and completed diagnostic
failures are recorded separately. Negative cases require their expected message,
location and notes and reject internal errors. Full coverage requires all 602
client names on both backends, independently of the suite exit codes.

The local manifest, incremental results, commands and logs are retained under
`/tmp/ferrum-prusti-stage3`. Four suite/backend harnesses run concurrently.
Durations include host contention and are used for watchdogs, not benchmarks.

## Reproduced source-version difference

`iterator/mut_element_replace_return_pass` has byte-identical native and JVM
Viper dumps, SHA-256
`a38759a0cfc830268b2d80136b9c0830a9eda3ce206f40abe0a3aabad800a774`.
With the effective Prusti settings above and `--includeMethods m_visit`:

| Backend | Result on that exact text |
| --- | --- |
| Ferrum `f686fde` standalone | Rejects the postcondition for insufficient predicate permission |
| Pinned Silicon `ff386aec` standalone | Same rejection and span `619.11--642.35` |
| Bundled Silicon `6b540aa4` standalone | Verifies |

The standalone Ferrum executable hash is
`f9a04bec73478f0e3a1898732f0ad286dbf87d70b28d22d70213f919c830ec70`.
The non-returning `mut_element_replace_pass` also reproduces this three-way
difference on its native dump, SHA-256
`06eb2997c6ad1519a90ec445c14769233d36bc901ca2ae09c7ace993b521185b`:
Ferrum and pinned Silicon reject at `714.11--737.35`, and bundled Silicon
verifies. That case's independently generated JVM dump differs; this comparison
uses only the exact native text on all three standalone backends.

The standalone replay's external bound is 240 seconds. Earlier source replays
without the full Prusti settings are retained as configuration-different evidence
and do not establish parity.

This reproduces a behavior difference between source versions. Its cause has
not been established; it does not justify changing Ferrum away from the pinned
source semantics. The raw replay commands, artifact hashes and outputs are in
`/tmp/ferrum-prusti-stage3/replay-replace`.

## Map membership adapter correction

The fresh hash suite exposed a native adapter defect: VIR membership conversion
constructed `MapContains(map, key)`, whereas Silver expects
`MapContains(key, map)`. The JVM factory already performs that argument reorder.
The original native run consequently rejected 22 hash checks with a map-type
consistency error; the bundled JVM passed all 51 checks.

Prusti commit `0ad015f11ac31ba76cbd942ee0c375e21b86b2a5` on
`codex/stage3-map-fix` corrects the native argument order. A real-Z3 regression
verifies a present key and requires exactly `assert.failed:assertion.false` for
a missing key, using the converted VIR and one reused frontend. Both native-only
and dual production builds pass. Their driver hashes are respectively
`61b2b8e710c692b454d48fdc69a20e3ac5bdd0358bb962cd2b935e133c664e3a`
and `9f08fcad676ed9b6dc3b98a771ab8e2fecacee41e7a5c2ccc77c4968eed19357`.

The complete corrected native hash rerun passes **51/51 checks**: 40 clients,
the specification library, the Rust compilation check and nine runtime controls.
It reuses the original fixture/harness snapshot `13674e5` with the corrected
binary built from the `0ad015f11` source tree. This is incremental validation of
the affected suite; the initial full matrix retains its original binaries and
results. The recorded rerun is
`/tmp/ferrum-prusti-stage3/map-fix/hash/results.json`, SHA-256
`a1c246c5a32f49a22c43ec047709bf52505b81691f529d0d81aa716a34f7ebc6`.
Other suites are audited for the same consistency failure before finalizing
the affected-fixture coverage.

The complete adapter library test run also exposed an obsolete fake-solver
handshake. The source-compatible version query reads its response directly;
the mock must answer that query before emitting the startup warning under test.
Test-only successor `a4d66141e` on `codex/stage3-warning-test-fix` repairs the
mock, and all **17 adapter library tests** pass with real Z3 and no ignored
tests. It inherits the map fix without changing production behavior; the
production binaries above remain the builds of `0ad015f11`.

## Shared unsupported expectation

`borrow/call_wand_shifted_projection` expects an unsupported-feature diagnostic,
but both original matrix backends accept it. A separate crate containing the
same source verifies on both backends; changing only the final assertion from
`value == 3` to `value == 4` produces the expected assertion failure at
`src/main.rs:14:5` on both. This supports an obsolete unsupported expectation
for that case and confirms that this deliberately false assertion is checked.
It is not a general soundness argument. The fixture was not edited to make the
original matrix pass. Sources, settings, commands and log hashes are retained in
`/tmp/ferrum-prusti-borrow-shift-probe/results.json`.

## Findings awaiting the full matrix

The borrow spec library and several borrow clients fail in the Prusti encoder on
both backends. Some also carry a generated verification failure without a Rust
source position. Shared encoder failures are separate from Ferrum port defects.
Several generic-array clients hit the verifier deadline on both backends;
other deadline outcomes differ. Equal timeouts are not compatible proof results.
Quiet repeats and remaining paired-case review follow the complete initial run.

The final matrix counts and any confirmed port defects remain to be recorded.
