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

## Current checkpoint and active work (2026-10-15)

Project /home/ebonnet/Bitbucket/lax/round-or-cut, branch main. HEAD dd01278
had the checked 313-module assembled oracle/search batch, Lean build and Lax
inspection passed. Last fully successful strict checkpoint: 135ab62 (292
modules). Main theorem is STILL OPEN. Root now imports 317 own modules.

CURRENT UNCOMMITTED WORK:
- NativeOracleContext.Protocol holds whole-state bounds, all buffer lengths,
  stack prefix/cursor, stride, frame length, fixed rounded width and node.D.
  collection_protocol derives this at actual child calls from parent Context
  and the collection anchor. Child callback was previously too strong: it
  quantified over arbitrary states without supplying the fixed width/frame.
  Fixed by giving Protocol explicitly to NativeNearExecution.Setup.recursive.
- NativeNodeProtocol proves actual phase-11 child entry inherits Protocol,
  proves pushed frame length, and turns a smaller-fuel Executes IH into the
  exact NativeCollectionChild.Recursive contract. Input has Protocol, graph
  order/prefix, target and recursion fuel. Eligible is a purely mathematical
  family indexed by fuel, order, graph, target and stack cursor.
- NativeRecursiveSetup separates numerical/solver requirements (Near, Oracle,
  Rounds) from recursive execution. Each computed part carries a proof it is
  Eligible. to_setup constructs the prior full search Setup using Children.
  No phase-execution or recursive-execution assumption is in these records.
- NativeNodeExecution.Bounds enumerates actual entry/initialization guards
  and buffer allocations. Search contains numerical search data and local
  work/branch bounds. Resources gives these uniformly over Eligible nodes.
  large_segment composes actual entry + initializer + complete search.
  executes closes ALL child calls by actual fuel induction, returning exact
  RecursiveAlgorithm.attempt and Protocol/graph/root-control preservation.
  Time and transitions satisfy NativeRecursionBudget.work local branches fuel.
  Executes also retains GraphData and RootData for the outer root driver.
- NativeOracleContext.RootData is equality of root.target/root.fuel between
  two environments. Near/oracle/update/round scan now preserve it. The scan
  carries a proof-only initial environment via WithRoot; no program changed.
- NativeNodeTrace.exhaustive_segment exports its actual two handler Runs so
  arbitrary Protocol/RootData framing can be derived from those Runs.
- NativeCoreExecution.command_spec composes frameSize + initializeRoot +
  all node executions + actual stack-empty root return + descending target
  search. Complete native unweighted command Spec is now CHECKED, conditional
  ONLY on Resources, root eligibility, scalar/mask/frame-size bounds.

SUCCESSFUL CHECKS (actual exit 0):
/tmp/qptas-child-protocol-build.log (from before environment refresh)
/tmp/qptas-root-data-rounds-build.log
/tmp/qptas-node-execution-build.log
/tmp/qptas-core-execution-build.log
Some earlier /tmp logs were lost when the user refreshed environment/cwd;
source files persisted. Current logs above except the first are present.
FULL 317-module root build passed actual exit 0:
/tmp/qptas-complete-core-root-build.log. No process running.
No Lax inspection/replay on this 317-module batch yet. Do not claim main closed.

## Remaining obligations (actual next work)

1. Construct NativeNodeExecution.Resources from chosen registered solvers and
   a single fixed root monomial. Existing numeric resource modules cover much
   of it, but the constructor is NOT done. Choose Eligible for hereditary
   graphs of order <= root N, targets <= their order, depth(order)<=fuel,
   and cursor+fuel*frameLength within allocated stack. Selected balanced
   parts inherit class/depth and selected costs give target bounds.
   Need all Bounds, NativeRecursiveSetup.Rounds, local step/time/branch caps,
   and exact frame extents. Keep certificate/trajectory heights separate from
   host word width to avoid circularity.
2. Assemble positive-size NativeQptasProgram Spec: frontend, graph activation,
   original accuracy read, root accuracy/budget, NativeCoreExecution Spec,
   weighted output. Preserve input.n/input.data/blowup.owner/weighted.positive
   through core, via actual source footprints (NativeCoreFrame helpers).
   Zero-copy branch already checked in NativeQptasZero.
3. Apply NativeFinalBounds and NativeQptasTransfer.qptas_of_spec, prove actual
   MainTheorem, then strict replay and closure audit with zero open statements.

## Lean pitfalls from this continuation

- Do NOT use all_goals first | exact bound1 | exact bound2 ... for large
  allocation guards: mismatched unification unfolds catalogs and timed out at
  2,000,000 heartbeats. Name each bound explicitly (large_input now does so).
- local is a reserved Lean token; use localCost.
- frameSize cfg footprints need simp [frameSize,initializeRoot,go,Com.wvars,
  Com.warrs]; decide cannot handle the free cfg literal, despite static writes.
- Root driver cost normalization used ring_nf then omega; opaque Nat products
  with different sum parenthesization were not solved by omega alone.
- write_stdin chars Ctrl-C successfully stops an obsolete compile session.
  Do not rely on PID kill across refreshed tool environments.

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
