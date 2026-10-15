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

Project /home/ebonnet/Bitbucket/lax/round-or-cut, branch main. HEAD 8652d11 is the checked 317-module complete core/fuel-induction
checkpoint (full Lean root build). Previous dd01278 had the assembled search
with Lean and Lax inspection passed. Last fully successful strict checkpoint: 135ab62 (292
modules). Main theorem is STILL OPEN. Root now imports 320 own modules.

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

## Further resource construction after 8652d11 (uncommitted)

- Fixed another over-strong interface: recursive domain is required ONLY
  for HEAVY parts. Added the heavy-cost premise to NativeCollectionExecution
  recursive callbacks and NativeNearExecution.Setup.recursive; actual
  iterations pass their known heavy condition. NativeRecursiveSetup.Near
  children-domain field now takes that condition. Empty/light parts do not
  recurse, and target=1 on an empty part must not require an eligible node.
- NativeRecursiveDomain defines actual Eligible: hereditary class membership,
  positive order <= root N, positive target <= node order, depth(order)<=fuel,
  cursor+fuel*frameSize<=capacity. root/child/heavy_child prove preservation.
- Exposed the SAME selected flow backend's SeparatorCorrect guarantee:
  NearOracle.exists_oracle_with_parts, NativeRecursiveOracle.exists_solvers_with_parts,
  NativeSolverSemantics.exists_solvers_with_parts. The original theorem
  signatures are preserved as wrappers, including NearOracle.exists_oracle's
  Lax conclusion metadata. This is essential to prove balanced actual pieces
  for the resource-domain IH without choosing a different flow function.
- NativeSelectedParts.selected derives conditioning cardinality, unit costs,
  and balanced actual computed pieces from that retained guarantee. children
  supplies the exact eligible-domain obligation for actual heavy queries.
  target_bound handles even zero costs; near_bound gives point coordinate
  bounds from the exact canonical certificate; near_feasible proves decoded
  feasible moments for the actual classification's nearby point.
- NativeEntryResources.bounds constructs ALL NativeNodeExecution.Bounds from
  resource<=R, k<=n, fuel<=2R+2, fixed amount(cfg,R)<=wordHeight, and that amount
  allocated in its listed entry buffers. amount is a fixed coefficient times
  (R+1)^4. This closes the entry/initialization block of the resource record.

All latest individual builds passed actual exit 0:
/tmp/qptas-heavy-child-core-build.log
/tmp/qptas-domain-and-selected-solvers-build.log
/tmp/qptas-selected-parts-resources-build.log
/tmp/qptas-entry-resources-build.log
FULL 320-module root build passed exit 0:
/tmp/qptas-domain-entry-root-build.log. Lax normal inspection ALSO passed
exit 0 (91 concepts / 165 proofs): /tmp/qptas-core-domain-inspection-summary.log.
Registered-external-assumption closure leaves ONLY MainTheorem.exists_qptas
open; audit at /tmp/qptas-current-closure-audit.json. Root restore passed.
No strict replay of the current batch. Last fully successful strict replay
remains 135ab62. The /tmp registered closure seed from earlier was lost.

Additional CHECKED modules, not all imported in root yet:
- NativeNearResources.bounds constructs ALL near numeric/allocation guards
  from root R, actual certificate height H, frame extents and stack capacity.
  wordHeight is explicit polynomial in R,H,S,cursor; certificate height is
  independent of host w. /tmp/qptas-near-resources-build.log exit 0.
- NativeRoundedResources.bounds constructs ALL rounded-update guards incl
  actual encoded query words, rational heights, host width and buffer sizes.
  /tmp/qptas-rounded-resources-build.log exit 0.
- NativeProjectionResources.bounds constructs ALL projection preparation
  guards/storage from root R (source rows, moment serialization, tolerance).
  /tmp/qptas-projection-resources-build.log exit 0.
- NativeSelectedLP.Program retains selected LP code, polynomials, coefficients,
  actual distance-query output fit and checked invocation. exists_program
  obtains it from existing native invocation theorem. certificate_bound uses
  THIS program's fit (resolves width-polynomial consistency issue).
  invocation converts actual varying query time/cost to uniform root caps,
  with exact functional projection output. /tmp/qptas-selected-lp-build.log exit 0.
- NativeSelectedNear.Program retains actual selected flow program/width/time/
  output/coefficient guarantees. setup assembles COMPLETE Near setup using
  feasible decoded moments and actual hereditary child domain. This includes
  bounded flow calls for ALL A (Near.flowCall has no successful-find premise;
  zero/missing coordinates handled by unconditional positive-quotient bound).
  /tmp/qptas-selected-near-build.log exit 0 before latest target-limit generalization.

Further CHECKED milestones (all still uncommitted):
- NativeSelectedOracle.setup: COMPLETE Oracle setup, assembling selected LP,
  selected flow, feasible near points and actual hereditary heavy-child domain.
  Only numeric word/space inequalities remain. /tmp/qptas-selected-oracle-build.log exit0.
- NativeOracleCutHeight: collect_cut_bound and near_cut_bound establish u<=n
  for the ACTUAL returned component cut; normal_height bounds BOTH far and
  near oracle cuts under the exact selected LP certificate width. Checked as
  SelectedRounds dependency (latest /tmp/qptas-selected-rounds-build.log exit0).
- NativeSelectedRounds.rounds: COMPLETE Rounds setup, with actual recursive
  oracle trajectory, all positive quadratic forms, same selected LP/flow,
  actual normal-height bounds, selected rounded program. near_time_affine
  proves the EXACT recursive-time coefficient (n+1)*childTime. Rounds.Bounds
  contains only numerical/array inequalities. /tmp/qptas-selected-rounds-build.log exit0.
- NativeSourceFrame: input.n/blowup.length and blowup.owner/image.output/
  weighted.output are absent from core writes and saved frames. Handles
  dynamic LP, flow, rounded programs using their generic framing facts.
  /tmp/qptas-budget-and-source-build.log has SourceFrame successful exit0.
- NativePolynomialEnvelope: small syntax-directed tactic builds pointwise
  polynomial majorants via checked add/mul/pow/eval lemmas. Earlier repeat/apply
  macro was too slow; replaced with Meta syntax inspection (proof-producing,
  no trusted new axioms). Unknown syntax raises explicit error.
- NativeSelectedBudget.exists_budget: ONE FIXED root monomial bounds all
  solver/buffer/precision demands, before root input. Uses exact selected LP
  width and polynomial eval monotonicity. CHECKED exit0 as dependency in
  /tmp/qptas-selected-execution-build.log (NativeSelectedBudget 3.2s).
- NativeLocalTime: all actual entry, large initialization, heavy search,
  component, near, projection/oracle local costs bounded by explicit ordinary
  polynomials in W and stride S. Includes polynomial theorem for localSteps,
  branches and localTime. CHECKED exit0 as dependency in same log (6.6s).

LATEST CHECKED MILESTONE (2026-10-15 around08:46 UTC):
- NativeRootWorkspace.bounds PASSED: concrete root layout and host height
  construct ALL NativeSelectedRounds.Bounds. This includes original-output
  extents, depth*frameLength stack, actual LP/flow demands and rounding guards.
- NativeSelectedExecution.resources PASSED: constructs COMPLETE
  NativeNodeExecution.Resources from those root inequalities and selected
  programs. No execution assumptions. fuel_bound uses positive frame length
  and actual stack capacity. This returns DATA: noncomputable def, not theorem.
- NativeCoreOutput.command PASSED: entire core NoWrite incl arbitrary virtual
  programs. /tmp/qptas-core-output-build.log successful exit0. Generic
  child_call/stack_return helpers prevent huge frame-list unification.
- NativeUnweightedExecution.command_spec PASSED: COMPLETE actual unweighted
  command Spec with all resource/solver/recursive obligations DISCHARGED.
  Remaining premises ONLY explicit numeric root inequalities and selected
  fixed programs. Returns exact RecursiveAlgorithm.solve answer, preserves
  input.n, blowup.length, blowup.owner, and output tape. guards derives frame,
  scalar and mask guards from hostHeight. cost uses actual recursion work.
  /tmp/qptas-unweighted-execution-build.log actual exit0 (3849 jobs).
- NativeQptasImplementation.exists_fixed PASSED: selects all actual solver
  functions, codes, coefficient lists, rounded program, semantic correctness,
  root envelope constants and root-budget constants ONCE for class C.
  /tmp/qptas-implementation-build.log exit0. Fixed oracle class is blowUpClass C;
  semantic correctness remains weighted original class C.

Root imports337 modules (all above). FULL ROOT BUILD PASSED actual exit0:
/tmp/qptas-337-root-build.log (session79127 completed). Need update counts from actual import list. NO strict replay
of new batch. Main theorem STILL open. Last strict success135ab62.

NativeQptasPositive.lean is now WRITTEN but NOT checked/imported/committed:
- copies/order/denominator/resource/workspace/budgetCost/cost definitions.
- positive_parameters and functional_result checked in current build before
  command_spec issues (infer from compiler absence; require final success).
- Bounds lists ONLY numerical frontend/root guards and one allocation bound.
- command_spec assembles ALL actual source stages and the checked unweighted
  core, ending in exact functional weighted solve output.
- Current build session65529 /tmp/qptas-positive-build.log. First iteration had
  many local alias mismatches; fixed by explicit change/typed bounds, normalized
  prepare outputs to N/H/copies, typed array room proofs; fixed chained trans
  parentheses, if True output extent simp, source program seq parentheses.
- Next inspect current compiler errors and finish Positive command_spec.

ACTUAL NEXT WORK:
1. Positive weighted source Spec (NativeQptasProgram.command). Core now DONE.
   Use Fixed C package to avoid repeating 20 solver/config parameters.
   NativeQptasZero.command_spec already covers zero-copy branch.
2. Final uniform width/time absorption into QPTAS.timeBound, invoke
   NativeQptasTransfer.qptas_of_spec; prove MainTheorem.exists_qptas.
3. Full build, lax inspection+strict replay, external-seeded closure ZERO open.
Do NOT stop merely at unweighted checkpoint.

Useful positive-wrapper design:
- copies := WeightRounding.copies (PositiveWeights.positiveWeights weights) ε.
  N=sum copies, H=WeightedAlgorithm.numbered G copies,
  D=RecursiveAlgorithm.accuracyDenominator N (ε/2),
  R=envelope fixed.E fixed.d N D, W=fixed.Q*(R+1)^fixed.e.
- extent=NativeRootWorkspace.extent cfg N W original_n.
  Source preparation, order, copy_graph_spec, OriginalAccuracy, RootAccuracy,
  RootBudget, UnweightedExecution.command_spec, WeightedOutput.command_spec.
- NativeBlowUp.numberedMatrix G copies definitionally equals adjacency H.
- RootAccuracy returns D and depth N; RootBudget returns R,W,stride.
- NativeStateBounds.initial + run supplies core bounded state. Array lengths
  invariant through all commands; source metadata framed using SourceFrame.
- WeightedOutput.discard_projected identifies functional weighted result.
  Positive N implies original n>0 and positive maximum; zero branch already
  handles both degenerate original cases.
- Input magnitude M=2^(rationalBitSize weights ε+1) has all input bounds in
  NativeInputBounds. Choose final host width coreHostHeight(cfg,W) +
  NativeRootBudget.guard fixed.E fixed.d fixed.Q fixed.e N D + fixed polynomial
  in n,N plus16*(rationalBitSize+1). This remains polynomial in R plus bits;
  DO NOT set w to numeric M (would make width exponential in rational bits).
- Frontend 2*M^4+3<2^w uses16*(bits+1). RootAccuracy guard has M*depth N,
  handled by bits+polynomial root height. Positive blowup has n<=N using
  NativeFinalBounds.original_order_le_copy_order (ε<=1), so ordinary extent S
  covers input.data/copy.counts etc once entry amount<=W.
- NativeLocalTime.polynomial cfg gives polynomial in W for steps+branches+
  localTime with S=2(W+1). Compose via NativePolynomialEnvelope and fixed
  W=Q(R+1)^e to obtain fixed monomial in R. Then
  NativeRootResource.recursive_bound handles depth recursion. Core cost
  (NT+26+68*(NS+3))*N+98 can be absorbed in a larger envelope.
- NativeFinalBounds.final_time/weighted_envelope handle final n,epsilon scaling.

Lean lessons:
- ALWAYS write spaces after <= unicode before identifiers beginning i;
  <=i notation otherwise parses InitialSeg (e.g. <=inputLength).
- gcongr may align +0 blocks wrong; simp only [Nat.add_zero] before gcongr.
- Alias-under-products causes omega to see distinct atoms: change to the
  exact source term or use explicit transitivity. Nat dimensions and catalog
  length are defeq but omega does not unfold: type-annotate catalog_two result.
- Avoid positivity on large inherited context/catalog aliases; Nat.mul_pos /
  Nat.pow_pos explicit is much faster.
- List.Disjoint has no Decidable instance; use simp [List.disjoint_left,buffers].
- RootWorkspace stack: simpa [extent,frameLength,Nat.add_assoc] using stack.
  simp only [if_pos rfl] left an if True guard and failed.

## Remaining obligations (actual next work)

1. Construct NativeNodeExecution.Resources from chosen registered solvers and
   a single fixed root monomial. Existing numeric resource modules cover much
   of it, but the constructor is NOT done. Choose Eligible for hereditary
   graphs of order <= root N, targets <= their order, depth(order)<=fuel,
   and cursor+fuel*frameLength within allocated stack. Selected balanced
   parts inherit class/depth and selected costs give target bounds.
   Entry Bounds now have a polynomial constructor; remaining fields are
   NativeRecursiveSetup.Rounds and local step/time/branch caps,
   and exact frame extents. Keep certificate/trajectory heights separate from
   host word width to avoid circularity.
2. Assemble positive-size NativeQptasProgram Spec: frontend, graph activation,
   original accuracy read, root accuracy/budget, NativeCoreExecution Spec,
   weighted output. Preserve input.n/input.data/blowup.owner/weighted.positive
   through core, via actual source footprints (NativeCoreFrame helpers).
   Zero-copy branch already checked in NativeQptasZero.
3. Apply NativeFinalBounds and NativeQptasTransfer.qptas_of_spec, prove actual
   MainTheorem, then strict replay and closure audit with zero open statements.

## Resource-constructor implementation notes

Use selected solvers from NativeSolverSemantics.exists_solvers_with_parts;
the returned SeparatorCorrect is for the SAME flow used by functional
correctness and native execution. NativeSelectedParts.children closes the
heavy-only domain field. Near point feasibility and certificate coordinates
are now checked in NativeSelectedParts.near_feasible / near_bound.

For a root R bounding ParameterResources.resource at every node:
- n,D,k,p,r,N,iterations,radius,precision <= R; floorPower <= radius <= R.
- Hcert = lpWidth.eval(queryBound R); Mnear=2^Hcert; costH=2*Hcert.
- Center bound can use 2^(80*(R+1)+4*R+1), separately from LP call's M.
- Far normal bound is 2^(2*Hcert+1); clearing adds (N+1) times its bits.
- Rounded height = NativeOraclePrecision.roundedHeight lpWidth R; trajectory
  guards come from NativeRecursiveOracle.trajectory_guards and domain depth.
- LP call M may be 2^(Hcert+100*(R+1)) to cover tolerance as well as certificate.
- LP query bits <=10^6*(R+1)^6; invocation wp/tp and cfg coefficients must
  refer to the actual chosen invocation theorem. Its fit premise suffices
  for a local certificate bound; avoid silently identifying a separately
  chosen OutputWidth polynomial with invocation wp.
- Flow uses h=2*Hcert and H=NativeLargeResources.heightExponent b n load k h.
  NativeFlowBudget/NativeOracleBudget bound guard, workspace and total time.
- W = fixed root monomial Q*(R+1)^e, rounded VM width v=W and S=2*(W+1).
  Host word height w may be a larger fixed polynomial in W plus 16*(ell+1).
  Heavy guards need wordExponent n r k p Hcert, a polynomial in R,Hcert,
  NOT a height derived from host w (would be circular).
- Allocate default extent S, except recursion.frames = depth(rootN)*frameLen
  and original-order output buffers = original n. Input.data fits S on the
  positive-copy branch using original_order_le_copy_order; zero-copy has its
  already proved separate Spec. frameLen=S*#frameArrays+#frameScalars >0.
- Domain stack inequality gives fuel<=rootDepth by cancellation of frameLen;
  rootDepth<=2*(log2 rootN+1)<=2*R+2. This supplies EntryResources fuel bound.
- Local oracle time must be bounded as oracleLocal+(n+1)*childTime; the Search
  record then derives localTime+branches*childTime, and actual fuel induction
  uses work. Choose uniform polynomial localTime/localSteps/branches in W.
  NativeRootResource.recursive_bound absorbs the amplified cost.

Remaining weighted glue needs core preservation of input.n, blowup.length,
blowup.owner and empty output. Use NativeCoreFrame scalar/array footprint
lemmas (metadata not saved/written) and show NoWrite for virtual interpreter:
RamVirtualProgram.instruction writes only VM output ARRAYS, never Com.write;
prove by cases/dispatch induction. RamPolynomial.command is NoWrite by list
induction. Primitive core cases other than 4/8/13 have static footprints,
definitionally equal to an all-empty-program config; those three have the
already checked projection/separator/rounded framing helpers.

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
