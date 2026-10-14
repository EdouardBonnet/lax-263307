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
arguments and many native RAM components are checked. The fixed unweighted controller is now defined; its complete recursive
execution proof and global resource bound have not been assembled. The residual difficulty appears to be this formal
composition; that is not a proof that no mathematical issue can remain.

Last strict replay: 292 own modules, 91 concepts, 165 public proofs. Closure
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

## Current locally checked work after the strict checkpoint

Commit `4cf6dec` is the 262-module strict checkpoint described above. Olean
restoration completed successfully. The following additions pass local Lean
checks (most also targeted lake builds); the full root build and strict replay passed (exit 0):

- `NativeComponentLoad`: actual part load, labels, cost/heavy/target decision.
- `NativeCoreMachine`: complete fixed 16-phase unweighted controller; frame
  footprints fixed before inputs. This defines the program, not its correctness.
- `NativeRootResource`: uniform positive-child bounds, polynomial envelopes and
  recursion amplification.
- `NativeMachineFrame`: frame/length invariants for phase segments. One-step handler extraction/frame lemmas are also checked.
- `NativeRootTransitions`, `NativeRootTrace`: concrete root transitions and
  descending-target trace, **conditional on recursive node traces**.
- `NativeRootBudget`: native computation of R, W=Q*(R+1)^e and stride 2*(W+1),
  including scalar-guard and time bounds.
- `NativeRoundTrace`: bounded scan trace, **conditional on concrete oracle/child
  steps**; its premise has not yet been instantiated.
- `NativeNodeTrace`: actual exhaustive/reject branches equal the functional
  attempt; large entry and full LP/catalog/rounded initialization reach phase 4.
- `NativeReturnTrace`: actual root-return and child-pop segments; the latter
  restores saved parent state/phase 12 and preserves the child's answer.
- `NativeProjectionTrace`: phase 4 preparation/invocation (using the existing
  solver spec), then all phase 5 branches, including the exact stored far cut.
- `NativeChildResources`: active child targets fit within positive child order,
  assuming the conditional costs lie in [0,1].
- `NativeCoreFrame`: all writes of the wrapped recursive controller are covered
  by its derived frame or explicit metadata exclusions; whole parent restoration
  follows from the saved frame plus preservation of fields outside it.
- `NativeNearTrace`: actual phases 6/7 store the LP point, select conditioning,
  reject if absent, or copy its mask and compute the cost vector.
- `NativeSeparatorTrace`: phase 8 invokes the known separator spec and initializes
  component traversal with the exact functional part order.
- `NativeComponentTrace`: actual phases 9/10/12, including part load/decision,
  light skip, heavy dispatch, collection completion, successful child lift/union
  and failed-child target-minus-one cut.
- `NativeChildTrace`: phase 11 prepares the induced graph, pushes the real parent
  snapshot at phase 12, and enters the child at phase 1 with decreased fuel.
  Its snapshot Run is the premise needed by `NativeCoreFrame.parent_restored`.

Successful logs: `/tmp/qptas-round-budget-build.log`,
`/tmp/qptas-node-trace-check.log`, `/tmp/qptas-concrete-traces-build.log`,
`/tmp/qptas-projection-dimension-build.log`, `/tmp/qptas-core-frame-build.log`,
`/tmp/qptas-near-trace-build.log`, `/tmp/qptas-separator-trace-check.log`.
Additional checks passed: `/tmp/qptas-frame-separator-build.log`,
`/tmp/qptas-component-trace-build.log`, `/tmp/qptas-child-trace-check.log`.
All 17 additions are now imported by the proof root (279 own modules).
Root build passed: `/tmp/qptas-controller-traces-build.log`.
Strict replay passed: `/tmp/qptas-controller-traces-replay.log` (10m05s kernel replay).
Closure audit: 91 concepts, 165 public proofs, only `MainTheorem.exists_qptas` open.
Those three drafts are now checked and imported (see the next checkpoint below).
The projection result/invocation specs now additionally retain `projection.n`,
needed by the far-cut handler; `NativeIntegerProjection` was adapted and checked.
`NativeLargeNode` has reusable Input/Output predicates; same concrete spec.
`NativeStackReturn` has a checked nonempty command branch and exact root result.

Next: recursive collection/rounded-step composition and the common global
resource invariant. Individual concrete phase traces are now available;
NativeRoundedControl supplies the phase-13 update Run directly. Do not mistake
conditional root/round contracts or known oracle invocation premises for the
missing complete recursive execution/resource theorem.

Integration facts:

- Heavy selection -> copy `conditioning.choice` to `conditioning.mask`.
- Part load -> `component.mask` and `unpack.mask`, canonical vertex labels.
- Phase 11 prepares child graph, snapshots parent at continuation 12, activates
  child and decreases fuel; child finishes at 14 and pop restores phase 12.
- Frame excludes stack controls and return tag/mask; includes parent phase/running.
- Rounded update resets `vm.width`; LP and flow calls overwrite it.
- Avoid `assumption` over many large dimension/resource inequalities: it can
  spend a million heartbeats unfolding mismatched dimensions. Supply the named
  bound explicitly. This fixed `large_input_frame` without weakening it.

## Refinement framework and follow-up batch (292 own modules)

The user identified **lax-62**, A Refinement Framework for the Word RAM.
It was previously missed. The proof-only dependency is now explicitly pinned
in `proofs/lakefile.toml` to registered commit
`0503df0eaf4e41104b9a3aa31e3e028b5adf7a0e`, `refinement-tower/proofs`.
Its RAM pin is exactly the existing `9394e531...`; Lean/mathlib also match.
`Lax62Proofs.Refine.Codegen.Cash` built successfully. Its NREST/Autoref/Sepref
layers were inspected; this batch uses `Codegen.solves_of_spec` in the final
uniform-program transfer. Existing native `Com` components remain usable.
Do not claim that importing the framework automatically closes the missing
algorithm specification.

All following additions passed local checks; the root build is recorded in
`/tmp/qptas-refinement-final-bounds-build.log`. The root build passed (exit 0). Strict replay passed (exit 0), log
`/tmp/qptas-refinement-final-bounds-replay.log`. Closure audit: 91 concepts,
165 public proofs, only `MainTheorem.exists_qptas` open. The first sandboxed
attempt failed fetching Lax62 (DNS), not a proof failure; the authorized rerun
succeeded. Restore root oleans before checking the following drafts.
Unverified drafts prepared during replay (not imported):
`/tmp/qptas-native-empty-output.lean` (actual empty-output routine and nonpositive correctness),
`/tmp/qptas-native-oracle-precision.lean` (actual canonical LP certificate and both-cut
normal heights in one root-polynomial bound), and
`/tmp/qptas-native-polynomial-budget.lean` (fixed monomial majorants and a computed
rounded workspace/precision budget). These have not been checked yet.

The 292-module batch contains:

- `NativeCollectionTrace`: complete collection-loop induction and identification
  with `ComputedRounding.collect`; its actual-iteration premise remains to close.
- `NativeTrajectoryResources`: numeric iterate height and positive quadratic
  form from the registered rounded trajectory and nonzero-cut theorem.
- `NativeExhaustiveResources`: binomial table word bounds and cubic exhaustive
  time in the uniform root resource.
- `NativeRecursiveOracle`: one fixed canonical encoded LP solver and flow solver,
  recursive child correctness, **actual recursive oracle cuts are nonzero**,
  and actual recursive trajectories satisfy height/positivity guards.
- `NativeQptasTransfer`: uses lax-62 to close descent from a complete command Spec
  plus explicit bounds to **one fixed RAM program**, at every larger width.
  The complete command Spec is still a premise, not a proved main algorithm.
- `NativeChildExecution`: actual call + recursive segment + actual pop/return;
  proves full parent restoration outside stack/return metadata.
- `NativeRoundedTrace`: actual phase 13 realizes the rounded cut outcome.
- `NativeOutputBounds`: genuine bounded command executions bound emitted words.
- `NativeDistanceQueryResources`: all program-field word bounds and genuine
  distance-projection query bit size from rational height.
- `NativeMomentEncodingHeight`: the checked native constructor bounds **all real
  moment-LP words** by height `100*(n+k+r+dimension+2)^3+10`.
- `NativeNormalHeight`: actual far certificate normal height, linear-bit
  denominator clearing, and failed-child integer-normal height `2*n+1`.
- `NativeProjectionQueryBounds`: actual scaled trajectory + real moment LP satisfy
  the projection height interface; query bits <= `10^6*(R+1)^6` uniformly.
- `NativeFinalBounds`: actual rounded blow-up order <= `2*n^2*ceil(inv epsilon)`;
  half-accuracy denominator <= `24*ceil(inv epsilon)*logarithm(N)`;
  converts root envelope on the blow-up plus polynomial rational-input work
  to the exact main-theorem QPTAS time expression with fixed constants.

`NativeChildResources.selected_costs` now proves the cost <= 1 premise from
feasibility and the actual successful heavy search. This discharges the
semantic premise used by the active-child target bound.

Local successful logs include `/tmp/qptas-collection-trajectory-build.log`,
`/tmp/qptas-recursive-oracle-build.log`, `/tmp/qptas-transfer-child-build.log`,
`/tmp/qptas-recursive-trajectory-check.log`, `/tmp/qptas-native-rounded-trace-check.log`,
`/tmp/qptas-query-height-build.log`, `/tmp/qptas-source-fields-build.log`,
`/tmp/qptas-native-normal-height-build.log`, `/tmp/qptas-native-final-bounds-check.log`.
The polynomial query bound is also included in the final root build.

Disk recovery: Lake's dependency-update cache hook filled the disk with a
second mathlib build. Generated builds in `hadwiger-counterexample` were
removed at the user's request; sources were preserved. The duplicate
`round-or-cut/proofs/.lake/packages/mathlib/.lake/build` was removed and replaced
with a symlink to the existing matching warm mathlib build. Last check: 13 GB
free. No project source or registered dependency pin was deleted.
The user explicitly extends standing command authorization to **lake**, as
well as git, gh, and lax. Keep this preference in the global instructions,
not in repository agent files.

## Remaining obligations

1. Prove the concrete phase wiring satisfies the node/round/component
   contracts, including frame preservation across nested child executions.
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
  `total + (4*cases.length+4)*steps + 4`. Root and bounded-round traces are checked conditionally; recursive
  node and concrete oracle-step traces remain missing. Avoid recursively expanding command syntax.
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

Related tool inspected: lax-218471 supplies compositional black-box **stack Turing-machine** programs. Not adopted; the existing real RAM oracle/frame machinery is already checked.
