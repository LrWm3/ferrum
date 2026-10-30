# Premeasurement validation

Premeasurement readiness evidence; no performance conclusions. Primary run is underway; these are earlier untimed gates.

Runtime: `afdf10cf59106c38d09df32939f1aa9c77d0b989`, immutable candidate v5 (527 files); performance tools revision `39bc221`; Prusti `a59ed917c1c3c4c4ca6ff1de12ad20d48491d021`. The plain and timed drivers were built separately against that runtime, with Rust 1.89.0, locked offline dependencies and opt-level 1. Their frozen build manifest records binary, source, dependency and toolchain hashes. Internal Silicon caches are ON for primary measurements.

The ten driver sessions and six comparisons passed. Eight fresh direct Prusti sessions covered four inputs with both backends. Eight parsed backend oracle sessions agreed; the negative result is `exhale.failed:assertion.false` at `mut_element_array_wrong.vpr@1786.10--1786.82`. The 96 configuration sessions cover four inputs, workers 1/2/4, branch off/on, fresh/reused, and both backends; all passed their recorded outcome and ID/position expectations. Three v2 CPU wrapper controls (native normal, source normal, native timeout followed by valid input) matched their baselines and reported complete observed process accounting.

Fresh native dump, JVM dump and copied backend fixture hashes match:

- `observation_pass`: `a0057d4998b80152fdaf1a1492b555b5d238bb4eca6b3f89c42225d7ae4a1546`
- `mut_element_array_pass`: `0708553587693a4f23c8d928a6359dd15fec34b6bbd9fef1bc5c2c054524efe7`
- `mut_element_option_pass`: `9876f7b0689ba6602fdb793bb7b07a93a81c66052ff48a06ecb353daa1c5744e`
- `mut_element_array_wrong`: `132ab8ca4e53de55d95fc50b0f60a2dbad04647f9f4a4e08115030b3a72b45e8`

Evidence (paths and SHA-256):

- runtime_manifest: `/tmp/ferrum-stage4-corrected-inputs/source-manifest.json` — `a86b833ab6e93c97491f99f3fdaaea7f70c88a263c322d9391057a702554e672`
- build_manifest: `/tmp/ferrum-stage5-phase-preparation/frozen-build-manifest.json` — `fa76208fff6623d4a3a0029531c9e890bbc3007c359d7f6c7b580157cd3de300`
- build_postflight: `/tmp/ferrum-stage5-phase-preparation/build-postflight.json` — `c57f5b3549ab3c89e3de414a735f2db6ffc57b3b7af6fe6a399bde07dcaafe70`
- driver_gates: `/tmp/ferrum-stage5-phase-preparation/behavior-gates/report.json` — `d23cacc76130e98ada06b0d9aa50ab0a179ff80eeb8c3f7d5a1f6b490ba807ca`
- prusti_calibration: `/tmp/ferrum-stage5-prusti-inputs/calibration-summary.json` — `ecf5ca8aa24ab336de23d3f71d8fadb6a918d7730469634a4347facdf68613b2`
- prusti_dump_parity: `/tmp/ferrum-stage5-prusti-inputs/calibration/dump-parity.json` — `3a4cfc5af55e487ea55f8a371435b5adc5a573cc883dad7b595ae0ff632f55f4`
- fresh_parity_recheck: `/tmp/ferrum-stage5-backend-inputs/fresh-byte-parity-recheck.json` — `04af8ad1ab79b79abcf3cc716767b27da47ae8f20394f6819f7b785c48e35300`
- backend_manifest: `/tmp/ferrum-stage5-backend-inputs/validated-inputs-manifest.json` — `5d8b30c71b90f60686104341eac30d0d36363842e53a05e0a4534e495ec680a5`
- parsed_oracles: `/tmp/ferrum-stage5-backend-inputs/oracle/report.json` — `7e6c574bafdec9179ee79505355ce96c31b6fef36b1e7ac10ad27ee56c9981d1`
- configuration_gates: `/tmp/ferrum-stage5-backend-inputs/config-gates/report.json` — `3ce807d51dbd96e31fffddab1e709c3096b2b1a0e6da1e08af4f448c93ec8e41`
- cpu_wrapper_gates: `/tmp/ferrum-stage5-z3-package-real-controls/report.json` — `a0d54fd78af237dc7a704d6296133940109b57e70a1fa9103c57035efbdd4868`
- cpu_baselines: `/tmp/ferrum-stage5-z3-real-controls/report.json` — `30678c71b48b75ed9b92614fca51b96ac543c44ef51b796b0542ada6d7441ac5`
- cpu_package_manifest: `/tmp/ferrum-stage5-z3-package/manifest.json` — `8b0be0c97121b98ff5ef36a4444ef2bfa0aa37994b853b447b042ce02fb56e53`

Limits:

- These checks are readiness and do not estimate performance.
- Driver gates use simple fixtures; warnings are retained but the 96 configuration gates do not assert warning parity.
- The selected observation native calibration was attempt 2; prior failed attempts remain in the calibration directory.
- CPU accounting completeness is bounded by observed identities and adopted processes; it is aggregate process CPU, not per-request or pure symbolic time. GNU time CPU is rounded.
- Source timeout behavior has an independently documented intermittent fault; no source timeout equivalence is claimed here.
- The four copied Viper files were checked for import/include tokens; this does not prove absence of every possible external dependency.

## Direct harness pilot

The complete direct-Prusti pilot passed all 12 expected requests with one event
per measured phase, root-only Cargo checking, valid timers, four distinct service
endpoints and four clean service shutdown audits. Failed preparatory attempts
remain recorded: v1 exposed missing server configuration and port reuse; v2 was
interrupted while correcting endpoint allocation; v3 exposed a harness variable
collision. The corrected v4 run made no production code changes. The service
reuses the process-level JVM object, but constructs a verifier per request; native
requests also construct a frontend. Later service requests are not proof of solver
reuse. See [the lifecycle audit](performance-service-lifecycle.md).
