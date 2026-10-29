# Advanced features and hardening checkpoint

Code checkpoint: `f686fde563e0e971d20a46eb8dd14e083a11e801`.
Source semantics remain pinned to Silver `c4f54b84703a04434b03e97bfea87dbd09870fd2`
and Silicon `ff386aec4664231dc6f2cb56d8d35f1623088363`. The reference jar SHA256 is
`bcab94591994788e41a62fa673f1001339ac2323ef58e27d428a7ca739c12726`.
These are compatibility and hardening checks, not performance measurements or
a claim that every Viper extension is implemented.

## Source behavior restored

| Path | Checked behavior |
| --- | --- |
| Generic domain `0236` | Axiom type variables remain rigid in their declaring domain. Bool/Ref/Perm instantiations retain only the two intended false assertions. External and cross-domain unconstrained parameters still default to Int with a warning. |
| Annotated Boolean `0950` | Result types follow nondominated overload substitutions. The original contract failure is reached; malformed Boolean operands remain rejected. |
| Heap triggers `0652` | Only reached callbacks contribute trigger terms and value definitions. An unreached callback retains one empty trigger alternative and the snapshot-map definition; the later false assertion remains visible. |
| Termination `specOrder` | The first nested termination metadata entry is selected. Both source files retain three tuple-false and three tuple-condition-false failures; duplicate decreases clauses retain three consistency errors. |
| Function permission warnings | Flag, spans and nested quantifier/let scopes match the source. The three warnings in `0950` match exactly. Warnings survive later type/plugin errors and reporter errors propagate. |
| SIF conditions | `low(t)` in branch/loop conditions retains the activation guard and normal/primed comparison. Three source failures, nested negation and positive active/inactive controls match. |
| SIF invalid inputs | Function/domain relational restrictions and unsupported goto statements report structured errors with original AST nodes. A mixed five-error input matches source order and spans; mixed warning/error output preserves its order and status. |
| Abstract read permissions | Invalid expressions and members accumulate 15 and four positioned consistency errors. Independent wand/misplaced-permission passes preserve both errors. Invalid-to-valid plugin reuse clears prior errors. |

The ARP `conditional`, `loops` and `quantified` fixtures match source diagnostic
lines and positions. `unfolding` has the same eight messages and positions after
whitespace normalization, but two native messages wrap differently; it is not an
exact-output match. Native frontend consistency errors retain exit status 2 while
the source CLI uses 1. Failure compatibility must compare the actual diagnostics.

## Logger ownership and cancellation

A successfully closed member logger is detached from the worker and its decider.
The run root retains the completed log. A failed close preserves the active
handle. A reused worker now both submits and executes standalone CFG join jobs;
the regression fails when only the production close fix is reverted. Public
advanced logging/state-reporting with parallel branches remains source-invalid.

Barrier-controlled cancellation runs with one and two workers. The two-worker
case blocks two distinct workers inside actual failure capture before cancelling
their solvers. It checks submission/execution, preserved cancellation and cleanup
errors, empty child handles, reaped Linux processes, detached failure data and
independent replay sessions. The integrated variant first executes 1,200
assignments to exercise cleanup after deep continuation execution. A test-only
expectation of a particular additional EOF diagnostic was removed: the required
cancellation and broken-pipe cleanup remain checked through typed outer errors.

## Native recursion

Shared same-thread checkpoints use a 2 MiB red zone and 16 MiB stack segments at
Silver expression rewriting/destruction, Silicon evaluation/statement execution,
and SMT term rendering. Small non-inlined entry wrappers precede the large
recursive implementations. Expression destruction moves fields in declaration
order, preserves shared ownership, and uses safe Rust. Solver contexts and
borrowed continuations remain on their owner thread. Production development
optimization level 1 is unchanged.

The recorded unoptimized iterator overflow retained 26,269 continuation frames;
large executor frames were approximately 80 KiB. Both retained iterator inputs
now verify at optimization level 0 through stdio Z3:

| Retained input | SHA256 |
| --- | --- |
| `mut_element_option_pass` Viper dump | `37298d96e005dd01f474b86e9f8f68f41094d9e875e1ecacc48d26d578b11158` |
| `mut_direct_pass` Viper dump | `0109a3ba5a44b7c724326c5e6bd3d16288a3228195d54e9b5081584f925b4279` |

These are older retained Viper dumps, **not fresh Rust verification matrix runs**.
Their local records are `/tmp/ferrum-stage2-stack-baseline` and
`/tmp/ferrum-stage2-stack-results`.

Permanent regressions cover 2,000-node rewrites on a 512 KiB thread, identity and
metadata preservation, destruction of 10,000 nested expressions with weak-handle
release and field-drop order, and rendering 4,000 nested SMT terms on a 256 KiB
thread. Corresponding baseline probes overflowed. The rendering test retains
individual nodes to isolate rendering from recursive term destruction. The
helper also checks returned errors, panic payloads, guard-drop order and thread
identity. A 1,200-statement positive/negative CLI control overflows before the fix
and retains exactly its intended failure afterward with one/two workers through
both stdio and linked Z3 4.16.

Checkpoint sizes are not a supported depth or total-memory bound. Parser paths,
other walkers and arbitrary statement, term or metadata destruction are not
established stack-safe. Segmented growth relies on the dependency's supported
platforms; the recorded checks use Linux x86-64. Stack allocation can exhaust
memory. This work does not claim reduced verification time.

## Validation and remaining compatibility scope

The composed source passes the default workspace all-target check, all 436 Silver
library tests, seven SIF and two ARP real-Z3 CLI controls, and the deep statement
control. The assembled runtime checks also cover all 369 Silicon and 21 root
library tests, with the corrected deep cancellation test rerun separately, plus
four public debugger tests and the function-permission warning CLI test.
The exact committed archive then passed all **826 library tests** in one serial
run: 21 root, 369 Silicon and 436 Silver, with zero failed or ignored tests.
The aggregate 300-second runtime watchdog began after compilation; its complete
log is `/tmp/ferrum-stage2-f686-tests.log`.

All real-solver runs explicitly set `FERRUM_TEST_Z3`; linked runs load Z3 4.16.
Test-only opt-level 0 overrides apply to all three workspace packages. Compilation
finishes before runtime watchdogs start. The exact code archive has 520 files;
its sorted SHA256 manifest is `/tmp/ferrum-stage2-final-f686fde.sha256`, digest
`cea688b1904c6e33989914a6990423e5cea41822a36decb706b8337ed329d329`.

The bounded extension audit distinguishes source restrictions from native gaps:
source consistency rejects indirect `forperm` binders; the public ADT encoder
uses its supported separate well-founded domain path; the source itself aborts
on the tested `if (lowEvent)` condition and simplified-unfold debugger leaf case.
These do not waive unrelated unsupported paths. Unsupported strings outside the
exercised fixtures remain unclassified for broader compatibility triage. See
[completion.md](completion.md) for the subsequent fresh Prusti matrix and broader
comparison stages. Performance measurement remains deferred.
