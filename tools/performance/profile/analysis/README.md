# Profiling analysis

`analyze.py` independently audited all 144 sessions and 48 matched blocks of the
completed run, with no integrity issues; see the [profiling report](../../../../porting/performance-profile.md).
It validates the 144-trial, 48-block seed-43 schedule; frozen spec/artifacts; session, timer and accounting files and hashes; exact proof and raw diagnostics; and independently rechecks timing, per-request phases and accounting joins. Missing, timed out, invalid or ambiguous observations are excluded from matched-block aggregates. Each block compares timed/plain and timed-with-accounting/timed wall ratios. Backend/case/configuration tables retain three repetition values where all blocks are eligible; phase first request and mean later requests remain separate by backend and phase. Solver CPU, version-probe CPU, total accounted CPU, residual and solver share are process accounting, not exclusive symbolic time. Nested phase spans must not be added and different source/native phase labels are not directly compared.

For a completed run, execute `python3 analyze.py --results RESULTS --spec /tmp/ferrum-stage5-profiling-preparation/spec.json --output NEW_DIRECTORY`. The analyzer does not invoke verifiers. Its filesystem audit reads all frozen artifacts and result records. Preserve the original evidence and choose a new output directory.

The `--runner` argument defaults to the sibling package runner (`../run.py`); use the explicit path for the staged copy. Backend-specific `request=None` phases describe emitted session boundaries, not whole-process JVM startup. Global integrity failure suppresses all aggregate tables.
