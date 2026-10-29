# c51 diagnostic comparison review

Base c51fc18babc883bd7868b4c65d63798481bb5bd2; `tools/compare_diagnostics.py` includes the fixture selection correction committed as `d81a149` (SHA256 1d6301afb163e7e750bcd4db56d39299752b31bb84d1ad11f173408ab60fcd48). Results `/tmp/ferrum-final-diag-c51-inventory.json`; 175 selected historical paired-failure cases, reference manifest and jar/individual fixture SHA verified. Fresh binary SHA256 6c9991eb13e6072b51cb2d36ba0d7b6032315c133cf92d587dcc9b72c5762254; Z3 SHA256 e583c4186a45e72411fa2cb2048401eed03f0f8e5f24694676a8f6271a50b765. Four parallel jobs; 20-second native watchdog. Imported dependency hashes are not independently covered by the reference verifier. Counts are comparisons of retained output, not corpus-wide semantic compatibility.

* 129 identical diagnostic line lists, including 0493c's six definition/call positions; this does not compare full semantic outcomes or all unnumbered warnings.
* 25 differing line lists: seven `all/import/standard_import/{basic,failing,local_and_standard,local_then_standard,loop_both,loop_local,loop_standard}` native bundled-resource vs Java classpath FileNotFound rendering; two `issues/silver/0266-{1,2}` native OS error vs Java FileNotFound including absolute path; counts and import-site positions match. Twelve malformed parser fixtures `0105[-1]`, `0138`, `0165`, `0183-{1,2}`, `0235-{1,2}`, `0500`, `0786`, `wands/examples/list_sum_applyold`, and `wands/new_syntax/LhsOldConsistency` are rejected by both parsers at equal source-position API spans; the Fastparse rule stack/found text differs. `0500` retains both errors at 83.1 and 125.43. Source internal rule trace line numbers need not equal the final source-position API (notably 0165/0183/0235/LhsOld). `0131` and `termination/errorMessages/cycleDecreases` expose small-set rooted traversal ordering gaps; the source-shaped correction is tested on simple and branching cycles. `0219` exposed a message-internal position bug (source call site 9.11 vs native definition 5.3); the corrected macro copier preserves the call site. `silicon/0950` is a source-valid semantic/typechecking gap: source reaches one verification error; native rejects two annotated-let requirements. Reduced witness `/tmp/ferrum-stage2-let.vpr`.
* Four multiline `0213{a,b,c,d}` errors: all reject at matching expression spans; source includes JVM Scala ParseTreeDuplicationError AST dumps and native uses concise resource-operand text, an explicitly documented adaptation.
* 17 unavailable: 13 have source harness timeout with no conclusive source diagnostic: `backend_types`, `comparisons`, `assume10QPwand`, `0175`, `0637`, `testTreeWand`, `testTreeWandE1`, `graph-marking`, `arrays_quickselect_rec`, `arrays_quickselect_rec_index-shifting`, `issue_0139`, `issue_0205`, `applying-twice-qp-predicates`; native itself timed out for eight of those and finished with diagnostic failures for five. `block_array` source reports one postcondition failure but native times out at 20 seconds; it is unresolved. `0652` source reports one intended assertion failure while native rejects the heap-trigger service; two termination specOrder fixtures each report six failures in source while native rejects duplicate metadata. These three are explicit stage-two semantic gaps.

Parser-engine wording, standard-import exception representation, and macro internal tree dumps are documented in `porting/differences.md`; Local filesystem errors now retain the actual import path, while native OS wording remains different. Cycles of at least five functions use Scala immutable hash-set iteration and retain a native rendering-order adaptation; source and native preserve membership. The 129 exact line lists still exclude multiline and warning ordering; no timeout or shared failure exit is treated as evidence of parity.

## Source details and focused follow-up

The source revisions are listed in `porting/sources.toml`. The references for
these corrections are Silver `parser/MacroExpander.scala` (expression macro
position adaptation and substitution), `parser/FastParser.scala` (import
loading), `ast/utility/Functions.scala` (rooted cycle queries), and
`ast/utility/Consistency.scala` (rendering the returned cycle set). The pinned
JGraphT `CycleDetector.findCyclesContainingVertex` uses a `LinkedHashSet`; its
`ProbeIterator` inserts members from the root's DFS path. Scala small immutable
sets preserve this insertion order; a five-member source fixture instead exposes
hash-set order. This distinction is about displayed names, not cycle membership.

The source and native runs use the same fixture inputs and Z3 path, one verifier,
`--disableCaches`, and a 20-second comparison watchdog. The comparison command is:

```text
python3 tools/compare_diagnostics.py --results <retained-results.jsonl> \
  --binary <fresh-ferrum> --z3 <z3> --output <new-output.json> --jobs 4 --timeout 20
```

The results and reference manifest hashes are recorded above and in the retained
JSON manifest; the comparison is limited by the retained source executions and
does not validate hashes of transitive imported files. Source and native output
must be inspected for all unavailable or multiline entries.

The follow-up checks reproduced the exact source call-site position for 0219,
the complete four- and three-error diagnostic lists for 0131 and cycleDecreases,
and the resolved missing path for 0266. A real-solver regression covers simple
and branching three-function cycle orders; parser tests cover the corrected
macro message and local import path. These checks do not update the 175-case
baseline counts above or establish a complete compatibility matrix.

## Consolidated successor validation

The same 175-case comparison after the focused changes yielded 132 identical
diagnostic line lists, 22 differing lists, four multiline reviews, and 17
unavailable comparisons. The three newly identical cases are `0219`, `0131`,
and `termination/errorMessages/cycleDecreases`. Local import failures still
differ in OS/JVM wording, but now include the path that actually failed. The
remaining semantic gaps and timeouts above are unchanged. The Silver library
suite passed 424 tests, and the real-solver cycle-order regression passed.
