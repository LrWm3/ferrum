# Compatibility corpus checkpoint

This records the cold CLI outcome check at Ferrum `d0d0ecb`. It is a triage
checkpoint, not the upstream annotation harness, full compatibility or a speed
measurement. In particular, ignore annotations are not interpreted and matching
nonzero exits do not establish matching errors or obligations.

| Outcome category | Cases |
| --- | ---: |
| `review_both_failed` | 659 |
| `same_success` | 515 |
| `reference_inconclusive` | 14 |
| `native_rejection_or_failure` | 2 |

All 1,190 fixture hashes and the Z3, Java and reference-jar hashes were checked
against the recorded baseline. Native execution used the same options, two harness
jobs and a 30-second per-file deadline. Reference outputs were reused from the
baseline rather than rerun. No timing comparison is valid for this run.

- Silver: `c4f54b84703a04434b03e97bfea87dbd09870fd2`.
- Silicon: `ff386aec4664231dc6f2cb56d8d35f1623088363`.
- Native binary SHA-256: `da8aaae2f76c8cdc14a3ea938b1077a5c3dd16e0ee5423f72242fe53f662bcbd`.
- Reference jar SHA-256: `bcab94591994788e41a62fa673f1001339ac2323ef58e27d428a7ca739c12726`.
- Z3 SHA-256: `e583c4186a45e72411fa2cb2048401eed03f0f8e5f24694676a8f6271a50b765`.
- Recorded result SHA-256: `7389f588454aa3ade1b1b9d6fd966f44393d7e22d430f564ea3dffa3d9f1ea3a`.

The baseline used Ferrum `cef5f36`. All four native-accepted/reference-rejected
cases now reject natively. Eighteen of nineteen native-only rejections now verify.
The remaining rejection is `all/issues/silicon/0715_2.vpr`, whose ADT constructor
terms are incorrectly rejected as triggers. A formerly successful case,
`examples/vmcai2016/linked-list-predicates.vpr`, hit the 30-second harness deadline;
a separate 120-second retry also timed out. It carries an upstream Silicon
ignore annotation. These results alone do not
identify the cause of its timeout.

The raw local artifacts are `/tmp/ferrum-upstream-rerun-d0d0ecb` and
`/tmp/ferrum-upstream-baseline-all-cef5f36`. The release source archive is
`/tmp/ferrum-corpus-d0d0ecb/ferrum`. Use `tools/compare_upstream.py` to reproduce
a fresh paired run with explicitly supplied native binary, pinned reference jar,
Java and Z3 executables. Retain its manifest and full outputs.

Diagnostic agreement among the 659 cases that failed on both sides remains a
separate review. Fourteen reference timeouts/inconclusive outcomes cannot establish
acceptance compatibility. Later targeted fixes need their own recorded validation;
this checkpoint is not silently updated to claim a new full corpus run.
