# Parser position checkpoint

The native parser previously walked the entire source prefix every time it
calculated a position. A bounded GDB sample of a slow parse found the verifier
thread in this scan at offset 206,256 of a 489,459-byte Prusti-generated Viper file.
The parser now indexes line starts and UTF-16 columns once per input. Lookups use
binary search over line starts and a column-array access. Temporary index storage
is approximately four bytes per source byte plus line-start offsets; it is released
when parsing that source finishes. Imported sources each have their own index.

All 14 fast-parser tests passed. Boundary checks cover astral/combining Unicode,
lone and repeated CR, LF, both CRLF boundaries, tabs, empty input and a parsed
expression span. The old and new CLI also produced byte-identical diagnostics
and exit codes for malformed Unicode and CRLF inputs.

| Same input, dev CLI | Recorded outcome |
| --- | --- |
| Previous `--parseOnly` | Harness timeout at 90.106 seconds |
| Indexed `--parseOnly` | Success in 0.923 seconds |
| Indexed full verification | Success in 231.110 seconds |

These are single runs on a loaded host. They demonstrate removal of a parsing
bottleneck and successful verification of the saved input; they do not establish
an end-to-end backend speed ratio. The previous parser source matches the frozen
base byte-for-byte. Full verification uses the same Z3/cache/one-worker options as
the pinned Silicon run, which also accepted this exact input. No consistency checks
were disabled. The full run's remaining time is not a solver-only measurement.

The Prusti native adapter constructs the Silver AST directly. This parser change
helps Viper-file/CLI workflows; it does not by itself speed up that conversion path.

Input SHA-256: `5b3be02aea40d1ff62443771afe0756f59eb931169226109dcf9025d6c2f5e4d`.

New CLI SHA-256: `c1b6f951ac93024d8e5e871c1d579d8e24217a7578e00d1b343364e4b9cfffe7`.

The binary uses Ferrum `c0eae48` plus the position-index patch. Raw local records
are `/tmp/ferrum-parser-pos-review/{parse-only,verify,diagnostic-parity}.json`,
with exact commands and output. The previous parse record is
`/tmp/ferrum-axiom-context-composed-parse.json`; the exact input is
`/tmp/ferrum-rust-matrix/shared-dumps/mut_direct_pass/native/viper_program/program-check.vpr`.
These input and executable artifacts are local and are not checked into the repository.

## Owned return-path selection

The return-frame selector now walks a supported subtree once, records its path,
and appends frames in outer-to-inner order. The receiver resumes that vector in
reverse. This removes the earlier repeated suffix searches and front insertion.
The initial Boolean eligibility probe retains its original allocation-free
implementation; only actual owned descent constructs a path plan.

An instrumented 128-negation chain visits 129 nodes in one path selection. A
model of the previous per-wrapper scan visits 8,384 nodes on that same chain.
This comparison excludes the initial dispatch scan, allocation, solver work and
execution; it is an operation count, not elapsed-time or end-to-end evidence.
Right callbacks and later transfer boundaries still clone frame vectors, so
right-heavy or repeated-transfer cases can remain quadratic. Descent remains
recursive. Worker and CLI regressions cover both operand order, nested old and
asserting returns, guarded fallback and cancellation.
