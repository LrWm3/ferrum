# Performance tools

All three experiments and independent audits are complete. The
[consolidated report](../../porting/performance.md) links the parsed-backend,
direct-Prusti and separate profiling evidence. These tools reproduce their
protocols with new immutable inputs and output directories; local raw artifacts
are identified by hash, not bundled into this directory.

These drivers and the serial measurement harness are separate from production
code. They retain the compatibility driver's verification flow. Plain drivers
add explicit cache policy; instrumented drivers additionally emit `@@PERF@@`
records with monotonic, inclusive wall durations. Neither variant changes the
runtime's optimization profile. Rust and Java source copies were built and
behavior checked before the first performance run; evidence and limitations
belong in the associated performance report.

## Build and freeze

Instantiate an isolated crate against an immutable Ferrum source snapshot:

```sh
python3 tools/performance/prepare_driver.py --runtime /absolute/frozen-ferrum --output /absolute/new-driver-crate
cargo +1.89.0 build --locked --offline --manifest-path /absolute/new-driver-crate/Cargo.toml --target-dir /absolute/new-driver-target
javac -cp /absolute/silicon.jar -d /absolute/new-plain-classes tools/performance/java-plain/SourceSession.java
javac -cp /absolute/silicon.jar -d /absolute/new-timed-classes tools/performance/java/SourceSession.java
```

The lock preserves the runtime's original dependency versions/checksums. Ferrum
is now a path dependency, so its dev-only serde_json edge is replaced by the
driver's direct dependency. Record resolved features, profiles, compiler, source
inventory, command lines and executable/class hashes for each build. The Rust
manifest template adds only a selectable runtime path and workspace isolation
relative to the initial measured crate. Preparation does not establish build
equivalence; the actual measured artifacts must remain identified independently.

Set `FERRUM_BENCH_INTERNAL_CACHES=on` for the primary experiment. `off` inserts
`--disableCaches`; an absent variable defaults to off for historical driver
compatibility. Other values and caller-supplied cache flags are rejected.
Prusti's `PRUSTI_ENABLE_CACHE=false` disables its outer result cache only.

## Run paired backend measurements

```sh
python3 tools/performance/run.py --inputs /absolute/frozen-inputs --tools-root /absolute/frozen-runtime --fixtures /absolute/validated-fixtures.json --output /absolute/new-results --pairs 5 --seed 42 --verifier-timeout 120 --outer-per-case 150 --reuse-cases 3 --internal-caches on
```

The frozen input directory supplies `source-manifest.json`,
`settings-stdio.json` and `evidence-stdio.json` using the compatibility evidence
schema. Settings identify both plain drivers with a hash-bound
`ferrum-bench-cache-policy-v1` capability marker, variant `plain`, and environment
key `FERRUM_BENCH_INTERNAL_CACHES`. The native marker names the executed binary;
the Java marker names `SourceSession.class` in the first classpath entry. All
executables, jars and classes must also appear in the frozen artifact inventory.
Fixtures specify explicit verified/failure outcomes and exact error ID/position
multisets. Establish these on the actual inputs before measurement.

The harness randomizes complete case/worker/branch/mode/repetition blocks and
backend order within each pair. It checks outcomes, record order, cleanup and
artifacts for every trial. Invalid and timed-out trials remain in the evidence;
there are no favorable-result retries. Use only complete valid pairs for ratios
and report exclusions. Fresh mode runs one request; reused mode runs three
requests in one new process and measures the aggregate session, not individual
request latency.

GNU time runs inside the owned-process supervisor around the verifier command.
Its primary wall includes startup, verification and shutdown, excluding Python
supervision and artifact hashing. Decimal timing resolution is usually 0.01 s.
CPU is process-tree accounting, not symbolic execution or solver-only time. RSS
is the timer's maximum resident set, not a sum of simultaneous workers' memory.
Source and artifact hashes are checked before/after trials and at final audit.
Hashing warms filesystem caches; a fresh process does not imply a cold OS cache.

## Phase attribution

`compare_sessions.py` compares full behavior and validates instrumented records;
`--plain` compares two plain drivers. Validate original/plain in cache-off mode,
then plain/instrumented under both policies, including recovery and cleanup.
Measure instrumentation overhead separately from primary plain-driver timing.

Rust records parsing, analysis, translation, consistency, preparation and
inclusive session verification, among other spans. Java keeps `runAllPhases`
unchanged and measures it inclusively: substituting individual phase calls can
change source behavior. These are not matching exclusive decompositions. Request
and phase intervals nest; worker/solver intervals overlap. Never sum them or
subtract overlapping wall spans to infer pure symbolic execution. Missing spans
are unavailable, never zero. Direct Prusti encoding/service measurements are a
separate experiment using its bundled JVM backend, whose source version differs
from standalone pinned Silicon.

Run `python3 tools/performance/test_run.py` for fake-runner checks of schedules,
cache marker validation, timer parsing and artifact mutation. These do not replace
real outcome, cancellation, session reuse or instrumentation checks.
