# QPTAS proof: current handoff

Updated: 2026-10-15. Read this first when resuming. WORKPLAN.txt retains
chronological details; checked Lean sources and successful process exits
are the evidence for proof status.

## Objective and honest status

Finish Lax263307, Bonnet–Chang Theorem 2: deterministic MWIS QPTAS for
hereditary classes with strongly edge-sublinear separators. The fixed
snapshot is round-or-cut.pdf. Applications/corollaries are out of scope.

**MainTheorem.exists_qptas remains open.** The complete fixed weighted RAM
program is now defined in NativeQptasProgram. Its complete execution Spec
and global resource invariant have not been proved. Mathematical algorithm
correctness and many actual machine phases are checked; conditional trace
lemmas must still be instantiated. Module/statement counts are not an effort
percentage. Do not claim completion from a successful Lax build.

## Checkpoint and current changes

Project: /home/ebonnet/Bitbucket/lax/round-or-cut, its own Git repo, main.
Lean cwd: proofs. Root: proofs/Lax263307Proofs.lean, now 304 own imports.
Latest strict checkpoint: 135ab62, 292 modules, 91 concepts, 165 public proofs;
closure audit left only the main theorem open. Logs:
- /tmp/qptas-refinement-final-bounds-build.log: exit 0.
- /tmp/qptas-292-module-replay.log: exit 0.
- /tmp/qptas-refinement-final-bounds-restore.log: exit 0.
Prior strict checkpoints: 5ee0ddd (279 modules), 4cf6dec (262 modules).

Current checked batch: twelve new modules and three existing-module updates.
Full root build and final Lax inspection passed; final strict replay remains
for a later completed milestone. See precise check scope below.
The 300-module root build /tmp/qptas-weighted-program-root-build.log passed,
exit 0. The two collection modules passed local Lean checks; 302-module root
build /tmp/qptas-collection-child-root-build.log passed, exit 0.
302-module strict replay completed: KERNEL REPLAY PASSED, inspection FAILED
solely because NativeEmptyOutput directly imported undeclared RAM Fill.
Fixed import to declared Lax62Proofs.Refine.Codegen.Harness. Log:
/tmp/qptas-refinement-final-bounds-replay.log. Root restoration passed, exit 0,
/tmp/qptas-collection-child-restore.log. No fully successful new strict replay yet.
Full 304-module root build passed, exit 0:
/tmp/qptas-weighted-zero-root-build.log. Lax build --profile passed, exit 0;
selected status log /tmp/qptas-weighted-zero-inspection-summary.log. Closure:
91 concepts, 165 public proofs; ONLY MainTheorem.exists_qptas remains open.
Post-Lax restoration passed, exit 0: /tmp/qptas-weighted-zero-restore.log.
Last FULL strict checkpoint remains 135ab62 / 292 modules. The newer
302-module run passed kernel replay but failed import inspection; that import
was fixed, and final inspection passed on the 304-module state. Do not describe
304 modules as fully strict-replayed. No build/replay is currently running.

- NativeOraclePrecision: actual canonical LP certificate heights and cleared
  far/component normal heights, using a polynomial in root resource R.
- NativeEmptyOutput: actual zero membership-vector emission, cost 24*n+14.
- NativePolynomialBudget: fixed polynomial majorants; covers query, rounded
  height, and rounded VM precision. Does NOT yet cover all other guards/work.
- NativeImageOutput: actual mask projection/emission for arbitrary repeated
  owner labels, cost 24*n+28*N+20.
- NativeWeightedOutput: actual blowup-owner projection, cost 24*n+44*N+36;
  proves it agrees with the functional nonpositive-weight filter.
- NativeMachineBounds: boundedness of all cells/arrays across phase segments.
- NativeSolverSemantics: same fixed canonical LP/flow choices support both
  native invocation and weighted functional approximation correctness.
- NativeQptasProgram: complete finite source/compiled program, checked layout,
  graph activation, and functional answer for zero-size blowup. Complete Spec
  remains open. Output array has exact original input order n as its length.
- NativeCollectionContext: concrete graph/cost/catalog/buffer/stack invariant,
  actual two-phase light iteration, and restoration from saved parent data.
- NativeCollectionChild: actual phase-11 call, child execution, stack pop and
  phase-12 reply preserve that invariant; success lifts/accumulates and failure
  writes the target-minus-one normal. Only the actual smaller-fuel child
  execution remains a premise. Does not yet instantiate all Iterations.
- NativeInputBounds: original order <= rational encoding length; all input
  words and parameter magnitudes bounded by 2^(ell+1). Local Lean check exit 0.
- NativeQptasZero: complete frontend/zero-copy/output branch Spec, including
  exact functional answer and original-length membership output; root checked.
- NativeCollectionContext.heavy_entry: actual two-phase heavy entry trace; full root checked.
- NativeFinalBounds.original_order_le_copy_order: n <= number of copies
  when maximum >0 and 0<epsilon<=1; local Lean check exit 0.
- NativeBlowUp.prepare_spec now also returns input.n=n. NativeBlowUp
  target rebuilt successfully; existing command_spec destructuring adjusted.
- RecursiveAlgorithm.independentSet_correct: extracted existing correctness
  argument for any fixed solvers with SearchCorrect; public claim unchanged.

The 292-module checkpoint includes NativeCollectionTrace, NativeChildExecution,
NativeRecursiveOracle, NativeRoundedTrace, NativeTrajectoryResources,
NativeNormalHeight, NativeProjectionQueryBounds, NativeFinalBounds and
NativeQptasTransfer. Its transfer uses registered lax-62 Codegen.solves_of_spec;
it still requires the complete source program Spec and bounds.

## Next actual obligations

1. Instantiate NativeCollectionTrace.Iterations from the checked light
   iteration, heavy entry and child_iteration, supplying the recursive
   smaller-fuel execution. Align each list index with its functional part.
   Preserve the parent graph/catalog/trajectory and collection context.
2. Compose projection/conditioning/separator/collection into actual oracle
   steps, instantiate NativeRoundTrace.Steps, then complete recursive node
   execution by induction on fuel. Preserve stack prefix/cursor on return.
3. Supply NativeRootTrace.Attempts with those node executions.
4. One uniform root envelope and polynomial working budget W=Q*(R+1)^e must
   cover ALL query, certificate, conditioning, separator, component, rounded
   guards, buffers, and local work. Current polynomial budget is only partial.
5. Complete NativeQptasProgram Spec: zero-size branch is now proved; assemble
   the positive-size frontend, graph
   activation/accuracy/budget/core/output, using the SAME canonical solvers.
   NativeRootAccuracy needs accuracy.n/d. The frontend stores them, but the
   current NativeBlowUp.prepare_spec exposes only input.n and tailInput prefix;
   derive their preservation or explicitly reload them from that prefix.
6. Absorb input/blowup/accuracy/resource bounds into final QPTAS bounds,
   apply NativeQptasTransfer.qptas_of_spec, add MainTheorem proof, strict replay
   and closure audit. No MainTheorem proof file exists yet.

## Integration constraints and resources

Input is unprefixed: [n] ++ n*n adjacency bits ++ weight triples ++ accuracy
triple. External RamPolytime queries prepend logical length; do not mix these.
NativeBlowUp.prepare preserves original input.n and produces blowup.length,
blowup.owner and blowup.matrix. NativeQptasProgram activates that graph before
computing root accuracy for epsilon/2. Config/C/d/Q/e are fixed before inputs.

Each saved working array can have extent S=2*(W+1); recursion.frames requires
separate depth*frameLength storage. image.output and weighted.output have
EXACT extent original n, outside the core frame. Preserve original owner and
input data across the core. LP/flow overwrite vm.width; rounded phase resets it.

Parent snapshot follows child-graph preparation and continuation 12. Parent
restoration excludes stack controls and returned tag/mask. Child costs <=1
are derived from feasibility; balanced children satisfy 3*card<=2*parent.
Actual oracle correctness/nonzero cuts use depth(n)<=fuel+1.

Use actual trajectory/certificate heights, not coarse VM width W (circular).
Trajectory height <=80*(R+1). Actual LP query bits <=10^6*(R+1)^6. LP certificate
height is the chosen invocation width polynomial evaluated at that bound.
Far subtraction height 2*M^2, clearing adds linear dimension factor; component
normal integer coefficients have height <=2*n+1. Root R envelope and weighted
log/accuracy absorption are proved in NativeFinalBounds.

## Validation and recovery

Keep terminal output short. Redirect builds/replays to /tmp; print selected
errors only. Require successful exit; an empty log is not success. NEVER run
Lean/lake or edit proof roots during lax strict replay (it relinks oleans).
After replay restore lake build Lax263307Proofs and wait for exit 0.
Strict check: lax build --replay --profile, about 10–11 minutes.
Closure seed: /tmp/qptas-registered-proof-closure.json; close conclusions whose
assumptions are closed until stable, then inspect all concept statements.
build-output.json is ignored; do not force-add. No push/submission authorized
by current action. User explicitly authorizes git/gh/lax/lake commands needed
for this task; do not ask again. Platform sandbox restrictions still apply.

Disk recovery removed obsolete generated hadwiger-counterexample build trees
and replaced duplicate project mathlib build with the warm build symlink:
/home/ebonnet/.lax/warm/v4.33.0-db584cd6d46c/.lake/packages/mathlib/.lake/build.
Do not delete that active warm build. About 13 GB was free after cleanup.

## Dependency pins

Lean 4.33.0; mathlib db584cd6d46c92f209a44c0f1c829460d327499d.
- RAM 808846: 9394e531cc51cb67a0214bca3f9264dfe97ba5c7
- RAM–TM 759944: 134e398cef46599371df99f10c9007bc34ba3868
- Treewidth 228581: 1e200ffac8b69e63b802f0aaf1dfee79561ca39a
- Leighton–Rao 455465 (registered): 9988b9c5399185cfb3ca2129ca7c807fd80c2885
- Expanders 920634: 4e1ce662f8ff75f2fa86d3a3973c871d3068c4c0
- LP 109476: 0a042604c7ae1ef4cd9a4c7d82eb902f313d4864
- Refinement lax-62: 0503df0eaf4e41104b9a3aa31e3e028b5adf7a0e
  proof-only dependency, same RAM pin; namespace Lax62Proofs.Refine.Codegen.
  Only Codegen.solves_of_spec currently used; do not claim full Sepref adoption.

Update this file after checked milestones and before context compaction.
