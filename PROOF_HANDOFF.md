# QPTAS proof: current handoff

Updated: 2026-10-14. Read this file first when resuming. It replaces the need
to reconstruct recent progress from conversation summaries. `WORKPLAN.txt`
contains the chronological record; Lean sources and completed verification
logs determine what is actually checked.

## Objective and honest status

Finish the Lax263307 proof of Bonnet–Chang Theorem 2: a deterministic MWIS
QPTAS for hereditary graph classes with strongly edge-sublinear separators.
The fixed paper snapshot is `round-or-cut.pdf`. Applications and corollaries
are outside the current scope.

**MainTheorem.exists_qptas is still open.** The mathematical correctness
arguments and many native RAM components are checked. A complete fixed RAM
program, its recursive execution proof, and its global resource bound have
not been assembled. The residual difficulty appears to be this formal
composition; that is not a proof that no mathematical issue can remain.

Last strict replay: 262 own modules, 91 concepts, 165 public proofs. Closure
audit left only the main theorem open. A count of 165/166 public statements
is not an estimate of remaining effort: the open statement contains
substantial implementation and resource obligations.

## Verified checkpoint and pending changes

Project: `/home/ebonnet/Bitbucket/lax/round-or-cut`, its own Git repository,
branch `main`. Root imports: `proofs/Lax263307Proofs.lean`.

| Commit | Checked additions | Strict replay log |
| --- | --- | --- |
| `99e3858` | Persistent rounded updates; finite machine traces; 234 own modules | `/tmp/qptas-native-rounded-machine-replay.log` |
| `5d54cde` | Node budgets, LP cache, rounded initialization, projection preparation; 246 modules | `/tmp/qptas-native-node-projection-replay.log` |
| `6ee6110` | Complete large-node setup, exhaustive returns, precision guards, recursion depth; 252 modules | `/tmp/qptas-native-node-entry-replay.log` |

All three replays completed successfully. No new external assumptions.

Current checkpoint: `NativeRootAccuracy` and nine new modules,
all strict-replayed successfully; 262 own modules are directly imported.
Root lake build passed (exit 0): `/tmp/qptas-recursive-handlers-build.log`.
Strict replay passed (exit 0): `/tmp/qptas-recursive-handlers-replay.log`.
Closure audit leaves only `MainTheorem.exists_qptas` open. Added modules:

- `NativeComponentCoefficient`: exact collected component coefficient;
  native cost `28*n+14`, masks read directly without a separate unpack buffer.
- `NativeComponentNormal`: canonical full normal in moment-catalog order,
  stored in `round.normal`; cost `(28*n+104)*N+20`. Proves clearing an already
  integer normal leaves it unchanged.
- `NativeOracleCut`: far projection clearing/storage and failed-child cuts.
  **Failure uses target t minus one**, with an actual decrement before writing
  the cut. Both handlers transfer to the rounded-update phase.
- `NativeComponentControl`: collection initialization/advance, successful
  child lifting and accumulation, failed-child cut, final found return.
- `NativeNodeDispatch`: computes node parameters and selects exhaustive,
  reject or search exactly as the functional algorithm; n<=1 bypasses logs.
- `NativeCollectionSemantics`: the sequential first-failure/union traversal
  equals `ComputedRounding.collect`; stored piece masks have the exact order.
- `NativeRoundedControl`: fixed update phase resets `vm.width`, performs the
  checked update, increments `round.i`, and either projects again or returns
  failure at `round.limit`.
- `NativeStackReturn`: pop restores the parent arrays/scalars/continuation,
  retaining the child's returned tag/mask; root return transfers to root phase.
- `NativeChildCall`: saves parent continuation and prepared graph state,
  activates child graph, passes target, decreases fuel, enters child phase.

The root-accuracy module computes `ceil(2/epsilon)`, balanced depth and the
accuracy denominator for epsilon/2 at cost `14*depth(n)+28`.
Its successful build log is `/tmp/qptas-root-accuracy-build.log`.
Other local check logs: `/tmp/qptas-component-coefficient-check.log`,
`/tmp/qptas-component-normal-check.log`, `/tmp/qptas-oracle-cut-check.log`,
`/tmp/qptas-component-control-check.log`, `/tmp/qptas-node-dispatch-check.log`,
`/tmp/qptas-collection-semantics-check.log`, `/tmp/qptas-rounded-control-check.log`,
`/tmp/qptas-stack-return-check.log`, `/tmp/qptas-child-call-check.log`.
All nine check processes exited successfully. Workplan/root imports and this
handoff are also modified. No main theorem proof has been added.

## Immediate next task

Root build, strict replay and closure audit passed. Olean restoration is running
in `/tmp/qptas-recursive-handlers-restore.log` (wait for the active build to finish). Four drafts were written under /tmp during replay and
have NOT been checked or added to the proof root:

- `/tmp/qptas-native-core-machine.lean`: complete 16-phase unweighted
  controller wiring existing handlers, root target/reply transitions, and
  fixed frame arrays/scalars derived from command write footprints. Workspace
  and accuracy initialization are preconditions; full execution still unproved.
- `/tmp/qptas-native-root-resource.lean`: root envelope uniformly bounds child
  parameters, fixed polynomial budgets and recursive amplification.
- `/tmp/qptas-native-machine-frame.lean`: scalar/array framing and invariant
  buffer lengths across entire finite phase segments.
- `/tmp/qptas-native-component-load.lean`: load each stored part, unpack its
  mask, compute labels and invoke the checked cost/heavy/target decision.

Check these drafts next (likely minor Lean API adjustments), then continue
constructing actual complete execution segments using the controller. Missing wiring includes projection preparation/invocation/reply,
near-point storage/conditioning/costs, separator output, component loading and
heavy/light branching, frame layout and root target transitions.

Concrete integration facts:

- Heavy search returns `conditioning.choice`; near costs reads
  `conditioning.mask`. Copy the selected choice before computing costs.
- Child preparation reads `unpack.mask`; load it from `component.mask`.
- `NativeChildCall` assumes the child graph and canonical vertex labels have
  already been prepared; its snapshot includes the child-reply continuation.
- `NativeStackReturn.pop_spec` proves actual restoration. Wrap it in the
  nonempty branch of its `command` when constructing whole-machine segments.
- `NativeComponentControl.childReply` expects the parent frame restored.
- The fixed arrays/scalars to snapshot still need to be selected from handler
  footprints. Exclude stack controls and return tag/mask; include parent phase.
- `NativeRoundedControl` now handles resetting the rounded virtual width and
  search-limit transitions; do not duplicate that logic.

## Remaining obligations

1. Assemble the fixed dispatcher and remaining wiring: projection, near replies,
   component loading/branching, frame layout, and root target loop. Individual
   entry/cut/child/update/return handlers are now locally checked.
2. Complete execution segments, by recursion fuel and bounded search/component
   loops, realizing `RecursiveAlgorithm.attempt` and descending targets.
3. One computed global workspace, word precision and time budget; instantiate
   existing parameter/resource and recursion amplification lemmas with the
   actual program. Include compiler and oracle simulation costs.
4. Weighted frontend, blowup at half-accuracy, output projection and emission,
   including empty/all-nonpositive cases; close `MainTheorem.exists_qptas`.
5. Strict replay and closure audit of the complete proof.

There is no `proofs/Lax263307Proofs/MainTheorem.lean` implementation yet.
Preview was served at `http://localhost:8137/lax-263307/`; current availability
has not been rechecked. No archive publication occurred in recent work.

## Reusable modules and integration constraints

All names below live in `proofs/Lax263307Proofs/`.

- `NativeMachineTrace`, `NativeMachineSegment`: fixed finite phase driver,
  segment append/child continuations, final concrete execution bound
  `total + (4*cases.length+4)*steps + 4`. Framework only; full handlers and
  traces are missing. Avoid recursively expanding command syntax.
- `NativeNodeParameters`, `NativeNodeAliases`, `NativeLargeNode`: actual
  class-dependent setup, catalog, moment LP/cache, precision and initial state.
- `NativeRecursionDepth`, `NativeRootAccuracy`: depth and half-accuracy setup.
- `NativeSmallAttempt`, `NativeAttemptReply`, `NativeMasks`: exhaustive base
  return and exact chosen-set mask. Mask packing already exists; reuse it.
- `NativeProjectionPrepare`, `NativeProjectionOracle`: cached LP restoration,
  scaled center/tolerance preparation, and registered solver invocation.
- `NativeProjectionResult`: kind 0 near point, kind 1 separating normal,
  kind 2 rejection. `NativeOracleCut.far` composes denominator clearing,
  normal storage and phase transfer (cost `193*N+40`).
- `NativeMomentStorage`, `NativeHeavySearch`, `NativeNearCosts`,
  `NativeSeparatorOutput`: near point storage, conditioning, costs, separators.
- `NativeComponentDecision`: exact cost, heavy/light test and child target.
- Child preparation/activation/return helpers and `NativeRecursionFrame`:
  saved parent working state, child graph and lifting its returned set.
- `NativeRoundedUpdate`: serialization, one fixed rounded-update invocation,
  exact persistent state decoding. **Reset `vm.width` from a computed global
  rounded width before every update**; LP/flow calls overwrite it.
- `NativeRecursionBudget`, `ParameterResources`, `NativeNodeResource`,
  `NativePrecisionResources`: checked abstract amplification/local bounds;
  not yet a complete program-wide runtime proof.

Use a separate `root.target`: exhaustive helpers write `target.*`, conflicting
with NativeTargetDriver's static callback protection. Parent continuation must
be saved before activating the child. Frame save/restore must exclude returned
tag/mask and its own stack/cursor metadata. Derive frame footprints from fixed
core handlers before wrapping them in frame commands; avoid circular syntax.

Main raw RAM input is **unprefixed**:
`[n] ++ n*n adjacency bits ++ weight triples ++ accuracy triple`.
RamPolytime oracle interfaces prepend their logical input length; the rounded
raw program does not. Keep these interfaces distinct.

## Resource plan to develop, not a completed proof

Existing bounds give a root common resource R of the form
`2^(C*(D*logarithm(n))^d)`. Child resources should be bounded by the root via
uniform parameter bounds. Choose fixed constants Q,e, then compute a working
budget `Q*(R+1)^e` with native logarithm/power commands. Cover local arithmetic,
oracle queries/results, precision, updates and array capacities with it.
Separate frame-storage extent from individual working-array extent.

Use actual trajectory and certificate height bounds, not the coarse virtual
output word width, when bounding arithmetic; otherwise precision requirements
can become circular. Rounded invocation time depends on the numeric iteration
index, not only its bit length. Weighted blowup size and `ceil(2/epsilon)` must
be absorbed into the final quasi-polynomial exponent; input-reading cost must
remain a polynomial in encoded input length. Handle empty inputs separately.

## Validation and recovery

- Check `git status` and current processes/logs before resuming an interrupted
  build. Do not start overlapping Lean/lake work and `lax build`:
  Lax replay relinks oleans.
- Run targeted lake builds from `proofs/`, e.g.
  `lake build Lax263307Proofs.NativeRootAccuracy`; redirect full output to
  `/tmp`, report only concise results. A successful process exit is required.
- Full strict check from project root: `lax build --replay --profile`.
  Recent replays take about 10–11 minutes, including long silent replay phases.
- After Lax replay, restore needed imports with a targeted lake build and wait
  for its successful exit before more Lean work.
- Search logs for `error`, not only `error:` (Lean also emits `error(...)`).
- Closure audit seed: `/tmp/qptas-registered-proof-closure.json`. Add conclusions
  whose assumptions are closed until stable; compare against concept statements.
- `/tmp` drafts/logs are supporting artifacts, not durable checked source.
  `build-output.json` is ignored; do not force-add it.

## Dependency pins

All dependencies below are registered; Leighton–Rao is **Lax455465**.

| Submission | Revision |
| --- | --- |
| RAM 808846 | `9394e531cc51cb67a0214bca3f9264dfe97ba5c7` |
| RAM–TM 759944 | `134e398cef46599371df99f10c9007bc34ba3868` |
| Treewidth 228581 | `1e200ffac8b69e63b802f0aaf1dfee79561ca39a` |
| Leighton–Rao 455465 | `9988b9c5399185cfb3ca2129ca7c807fd80c2885` |
| Expanders 920634 | `4e1ce662f8ff75f2fa86d3a3973c871d3068c4c0` |
| LP/ellipsoid 109476 | `0a042604c7ae1ef4cd9a4c7d82eb902f313d4864` |

Lean: 4.33.0. Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`.
Foreign proof sources are under `proofs/.lake/packages/Lax*Proofs/proofs/`.

## Keep this file current

Update after each checked milestone or change of next task, and before a
handoff/context compaction. Replace stale current-state entries instead of
appending another long history. Record check scope and outcome precisely;
distinguish drafts, local passes, strict replay and main theorem completion.
