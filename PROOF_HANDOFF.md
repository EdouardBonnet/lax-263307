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

## Checkpoint and current work

Project /home/ebonnet/Bitbucket/lax/round-or-cut, branch main. Previous checkpoint
237f1d1 had 304 modules (root build and inspection). The assembled search
batch is checked by Lean and archive inspection.
Root now imports 313 own modules. The main theorem is STILL OPEN.
Last fully successful strict checkpoint remains 135ab62 (292 modules).

Five new modules and three existing-module changes are currently uncommitted:
- NativeCollectionAnchor: a frame covering all parent data outside actual
  collection work and metadata exclusions. Child activation is deliberately
  NOT excluded; its changes are undone by proved stack restoration. Includes
  exact preservation of NativeRoundedTrace.StoredState.
- NativeCollectionExecution: actual light/heavy iteration composition,
  functional list-index alignment (duplicates permitted), and complete
  collect_segment with explicit transition/time bounds. Its invariant is
  Context plus Anchor. The ONLY recursive premise is actual smaller-fuel
  child execution at the entry produced by the actual child call. This
  instantiates NativeCollectionTrace.Iterations; no abstract Iterations
  premise remains in the complete collector theorem.
- NativeFlowBudget: polynomial bounds for actual large-capacity height,
  flow query size, wordHeight, spaceBound and complete separator time;
  one fixed root monomial covers all three flow guard/space/time bounds.
- NativeOracleBudget: one fixed Q,e covers LP query workspace, certificate-
  derived cut height, rounded VM precision, LP word/time polynomials, fixed
  allowances, and actual flow guard/workspace/complete separator time.
  Still requires n/load/k<=R and flow input bit height bounded by the selected
  LP height polynomial. It is NOT yet the complete global invariant/time proof.
- NativeOriginalAccuracy: actual 18-cost read of original epsilon numerator
  and denominator from retained input.data at original n*n+3*n+[1,2].
  This closes the accuracy-field interface without relying on an unexposed
  frontend postcondition.
- NativeCollectionContext light_iteration and heavy_entry now also return
  Anchor from their initial environment to the final environment.
- NativeCollectionChild now names Recursive, uses a non-generalizing result
  match, and returns Anchor initial/final in addition to the reply. The actual
  child call/pop/reply restores parent trajectory/cache data as a conclusion.
- NativeQptasProgram positive branch explicitly calls NativeOriginalAccuracy
  after copyGraph and before NativeRootAccuracy. Zero-copy Spec still checks.

Successful checks (actual exit 0):
- /tmp/qptas-collection-framing-build.log
- /tmp/qptas-collection-execution-check.log
- /tmp/qptas-full-collection-root-build.log (306 modules)
- /tmp/qptas-flow-budget-build.log
- /tmp/qptas-oracle-budget-check.log
- /tmp/qptas-original-accuracy-build.log
- /tmp/qptas-collection-oracle-root-build.log (FULL 309-module root build)

Validation of the 309-module batch completed successfully: lax build --profile
(actual exit 0), 91 concepts / 165 public proofs; closure audit found only
MainTheorem.exists_qptas open. Restored lake build Lax263307Proofs successfully
(actual exit 0), /tmp/qptas-assembled-collection-restore.log. No process running.
No full strict replay has been done on this 309-module batch.

Previous checked components remain in source: canonical NativeSolverSemantics,
NativeQptasZero, NativeWeightedOutput, NativeInputBounds, NativeOraclePrecision,
NativePolynomialBudget, NativeQptasTransfer and all native phase traces. The
last closure audit was 91 concepts / 165 public proofs, only the main open.

## Current assembly (2026-10-15, latest user: “so assemble them”)

Four new modules are being added to the prior batch:
- NativeOracleContext: common parent catalog/moment/LP cache, fixed scalar
  data, array extents, stack protocol and rounded VM width. Frame proofs
  for actual forward phases and restoration from complete collection. of_large
  derives this context and StoredState 0 (1,0) from NativeLargeNode.Output
  plus the incoming workspace/stack protocol.
- NativeNearExecution: actual phases 6/7/8 plus complete collection and
  recursive children. Computes the exact functional near result; derives
  preservation of the complete parent context and stored rounded state.
  Bounds/Setup contain inequalities, solver Specs and the smaller-fuel child
  premise; no assumed conditioning/separator/collection phase executions.
- NativeOracleExecution: phase 4 plus all phase-5 branches and complete
  near execution. Produces stopped result or the exact normal at phase 13.
  actual_reply identifies this computation with ProjectedOracle.run and
  RecursiveAlgorithm.attempt on canonically relabeled child graphs.
- NativeOracleRounds: actual rounded update plus the complete oracle
  instantiates NativeRoundTrace.Steps. Invariant includes exact functional
  trajectory, stored state and common parent context. Fixed rounded program
  contract is supplied by NativeRoundedControl.exists_program. search_segment
  assembles the complete bounded search without an assumed Steps premise.

CHECKED (actual exit 0): /tmp/qptas-oracle-execution-build.log,
/tmp/qptas-oracle-rounds-build.log and FULL 313-module root build
/tmp/qptas-composed-search-root-build.log, including Setup/search_segment/of_large.
No sorry/axiom in the new modules. Lax build --profile inspection passed
(actual exit 0), 91 concepts / 165 public proofs; selected status log:
/tmp/qptas-composed-search-inspection-summary.log. Closure audit: ONLY
MainTheorem.exists_qptas remains open. No strict replay on this batch.
Root restore lake build Lax263307Proofs passed actual exit 0:
/tmp/qptas-composed-search-restore.log. No process running. Checked batch
checkpoint: Assemble complete oracle execution and bounded native search.

## Next actual obligations

1. Use NativeOracleContext.of_large and NativeOracleRounds.search_segment
   to assemble the large branch of NativeNodeTrace. Complete node execution by induction on fuel,
   supplying the smaller-fuel child premises in the setups. Derive balanced
   child class/depth and target bounds from actual selected costs/cuts.
2. Instantiate NativeRootTrace.Attempts with complete node executions.
3. Prove the common resource setups for actual trajectories and certificates:
   use NativeOracleBudget for the LP/flow/rounded joint monomial, extend it
   to non-oracle arithmetic guards, conditioning, buffer extents, stack
   storage and recursive time amplification. No complete global resource
   invariant/time proof exists yet. Avoid certificate/host-width circularity.
4. Assemble the positive-size NativeQptasProgram Spec: frontend, graph
   activation, explicit accuracy read, root accuracy/budget, core and weighted
   output. Zero-size branch checked in NativeQptasZero.
5. Apply NativeFinalBounds and NativeQptasTransfer.qptas_of_spec, add actual
   MainTheorem proof, strict replay and closure audit with zero open statements.

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
