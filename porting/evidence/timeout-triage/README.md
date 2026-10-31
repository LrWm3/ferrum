# Timeout follow-up evidence

`observations.tar.gz` preserves the investigation in
[timeout-followup.md](../../timeout-followup.md). Its SHA-256 and every archived
member's hash appear in [the machine report](../../timeout-followup.json).

The archive contains all 49 untraced session records, four diagnostic captures,
full raw outputs, per-profile plans, the original 15 selected entries, all eight
fixture files, pre/postflight audits, build log, and Python runner and collector.
Diagnostic directories retain relay wrappers, commands, SMT bytes, timestamped
chunks, prover comments and analyses. The wands captures also have a comparison.

Raw working files were created in `/tmp/ferrum-timeout-triage-2df948c`. Absolute
paths identify that execution environment. Fixture copies preserve input bytes;
moving them can change source-position/quantifier names, so replay from different
paths is not automatically byte-identical. Timeout captures retain their
unanswered final check and are not complete solver transcripts.

Build source is Ferrum `2df948c9014de33b7baa13599eaf9d5078906b28`, with archive
hash and unchanged-file audit recorded separately. Build targets and reference
executables are not duplicated here; their hashes and pinned revisions identify
them. No observation is omitted because it was slow, timed out, or contradicted
an earlier hypothesis.
