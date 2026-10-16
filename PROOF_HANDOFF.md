# QPTAS proof handoff

Updated 2026-10-16. Read this first when resuming. WORKPLAN.txt keeps the
chronological history, including earlier incomplete checkpoints.

## Current status

### Direct external QPTAS statement (2026-10-16, locally validated)

The user requests removal of the redundant `Lax263307.QPTAS` concept.
Deleted that module and its root import. The main concept and proof now
conclude `∃ alg, QPTAS (problem := problem) alg (instances C)` using
`open Lax213208.QPTAS (QPTAS)` and `IndependentSetProblem`. No local
`HasQPTAS` predicate remains. Removing the wrapper left `QPTASRuntime`
isolated in the concept import graph. Moved that internal formula to
`Lax263307Proofs.QPTASRuntime`, updating the proof imports and root indexes.
The algorithm proof and time-bound formula are unchanged. Checked inventory:
84 concepts (67 lemma, 16 definition, 1 theorem), 135 claims/proofs, 344 proof
modules. Initial build session 96484 was stopped to include this relocation.
Full `lax build --no-color --profile` passed (session 94574, exit 0):
concepts 15s, proofs 1m09s, statement inspection 15s. Log:
`/tmp/qptas-direct-build.log`. Closure audit passed: all 135 claims proved,
all in headline ancestry, no admissions or unmatched proofs. All 84 local
concepts are connected, and the exported headline names
`Lax213208.QPTAS.QPTAS` directly. Audit: `/tmp/qptas-direct-audit.json`.
Local main-theorem preview links to `../lax-213208/Lax213208.QPTAS.html`;
all 19 nodes in its displayed neighborhood are connected, and neither removed
concept appears. Preview: `/tmp/qptas-direct-preview.html`.
Next: commit/push and resubmit; record the source and archive workflow.

### Comment and bibliography revision (2026-10-16, validated and submitted)

The user requested removal of comment attributions, an arXiv source reference,
and resubmission. Removed all 88 attribution sections from 73 local Lean files,
retaining the mathematical notes about component cuts and entropy. Moved the
rational reader's source/license provenance from its comment to `NOTICE`.
Updated the bibliography to arXiv:2610.16025 (verified on arXiv, submitted
12 October 2026). A comparison after removing comments confirms no Lean
declaration or proof changed in any of the 74 edited Lean files.
`git diff --check` passes. Full local `lax build --no-color --profile`
passed (exit 0; quiet log `/tmp/qptas-arxiv-build.log`): concepts in 1m02s,
proofs in 12m04s, statement inspection in 16s; 86 concepts, 135 proofs.

Committed/pushed source: `4e701623a80aace39fc00986b497d9bb3b4adcfe`.
Resubmitted with `lax submit --force --no-color` (session 34534), so archive
validation runs independently in parallel without a duplicate local build.
Archive workflow: https://github.com/lax-archive/lax/actions/runs/38949896864
Dispatched 2026-10-16T18:46:26Z; completed successfully. CLI exited 0:
archive rebuild 22m35s, public-record publication 1m32s. The updated draft
was accepted. The same 45 nonblocking warnings remain.

### Revision to the registered approximation framework (proved, archive-validated, submitted)

User requests QPTAS from lax-213208 and direct use of higher-level program
models (not a bespoke raw-RAM statement). Baseline is completely proved,
validated, and published below; do not redo the algorithm proof.

- lax-213208 was registered by workflow 38935326509, archive commit
  d688cde657b028b38c76d65bb36866d0fbb0640e. Its immutable source is
  EdouardBonnet/lax-213208@180b8ec1e851a4948b7a3c77d001e29df8a32dad.
- Added that concept dependency and its structural-arena dependency
  Lax560851@2748fdc0afc0b4f729b7775ca6475ba08129418a to both lakefiles.
- Registered QPTAS takes ONE program, precision k>0, approximation ratio
  1+1/k, and quasipolynomial time in the binary size of a structural arena.
  Input is the arena of (k, instance), not the current flat input tape.
- MWIS problem: standard list-of-naturals structural presentation
  of the canonical graph/weight packet (n, adjacency matrix, rational triples),
  identity output encoding of the membership vector. Feasibility interprets
  the packet; objective is nonnegative total weight (positive part for signed
  inputs). Every graph/weight pair has its canonical represented input.
- Keep the already checked NativeWeightedExecution.command_spec as the
  algorithm interface. Change final transfer to use lax-62's
  Codegen.computesInTime_of_spec directly, then registered QPTAS.
- A proved structured-command adapter reads structural input and k, uses
  epsilon=1/(k+1), and run the existing command on the flat instance packet
  followed by [0,1,k+1]. Marshaling, uniform time/width bounds,
  and the conversion from (1-epsilon) to ratio 1+1/k are checked.
- Reuse the stronger detailed running-time estimate internally. The new
  public headline must conclude the actual lax-213208 QPTAS predicate.
- Checked new `IndependentSetProblem` concept and proof: canonical packets
  recover the graph and rational weights; all feasible outputs are independent
  sets; accuracy 1/(k+1) gives the archive ratio 1+1/k, including signed weights.
- Checked `BufferedCommand`: injective renaming isolates the source state;
  redirects reads to a prepared array, with a proved factor-eight bound and
  monotonicity of the word bound. Uses the structured command semantics.
- `StructuralPacket` and `StructuralFrontend` pass Lean. They decode the
  standard postorder arena into that buffer, without advice.
- `NativeArchiveExecution` passes Lean: one fixed structured command, compiled
  directly with lax-62's `computesInTime_of_spec`, satisfies archive RunsWithin.
- `ArchiveRuntime` passes Lean: original source time plus all structural input,
  buffer, compiler, word-width and layout costs fit the registered envelope.
- `ArchiveQptas.exists_qptas` passes Lean and proves the actual external QPTAS
  predicate. Final wrapper now uses it; `QPTAS.HasQPTAS` is a specialization
  of lax-213208, not a custom raw-execution definition. Removed obsolete
  `NativeQptasTransfer.lean` and its imports.
- First full Lax build compiled every concept and proof but rejected outdated
  root imports and an external axiom in the problem's injectivity field.
  Fixed root indexes (86 concepts, 343 proof modules), and replaced that field's
  proof with direct constructor injectivity, without external axioms.
- Corrected full Lax build passed (exit0, 2m14s): 86 concepts, 135 proofs,
  no errors. 67 LEM, 18 DEF, one THM. Closure/admission audit passed: all 135
  claims closed and in headline ancestry; no unmatched proofs or admissions.
  Definition audit confirms HasQPTAS is the external predicate and the problem
  definition uses only propext/Classical.choice/Quot.sound.
- Logs: /tmp/qptas-framework-final-build.log, /tmp/qptas-definition-audit.log,
  /tmp/qptas-framework-audit.json.
- Source committed and pushed: 64fa63b6d0695e92909f87d75e77fc9802742106.
  `lax submit --no-color` dispatched archive workflow 38940528328
  (2026-10-16T17:33:02Z). It succeeded: validation completed at18:05:22Z,
  publication at18:07:08Z. CLI exited0 and confirmed the updated public draft.
  Archive commit: e9fd08bddcc64e7b475f00685026e1f2ca204074. Issue201 result
  acknowledges this immutable source and accepted the Website rebuild event.
- Local preview runs at http://localhost:8136/lax-263307/index.html (session
  61293). All 121 local/external concept nodes are connected; credits are
  correct and the QPTAS page links directly to lax-213208. Audit saved in
  /tmp/qptas-framework-preview-audit.json. New preview graphs render in the
  browser from the embedded graph-data JSON, so the old SVG audit cannot run
  directly on unrendered preview HTML.
- No proof or submission work remains. Website propagation is being checked;
  at18:34Z the live QPTAS page still served the previous version, while the
  local preview already showed the new version. Do not confuse propagation
  delay with incomplete proof or failed archive validation.
  Website repository: lax-archive/lax-website. Runs38944975469 and38945733628
  were superseded/cancelled; replacement run38947961285 (18:31:10Z) was still
  active at the final check. The accepted archive snapshot is authoritative.

Useful local sources: ../approximation-algorithms/concepts/Lax213208/;
its .lake/packages/Lax560851 contains the registered structural encodings.
Lax62 codegen is in proofs/.lake/packages/Lax62Proofs/refinement-tower/.
No subagents. Keep logs quiet; no further permission needed for git/gh/lax.

### Draft cleanup completed and submitted (2026-10-15)

The user requested submitter credit for Édouard Bonnet, Codex 6, and Codex
6.1; lemma labels for supporting results; removal of unused proof-network
components; cleaner concept namespaces; and a clean `HasQPTAS` conclusion.

- Manifest credit updated. The headline is the only theorem concept;
  supporting claims are lemmas, and definition-only concepts are labeled
  definitions.
- Audited actual Lean declaration dependencies. Of 50 claims outside the
  original headline ancestry, 31 were unused and were removed. The other 19
  were used through direct proof calls; 29 call sites now use their concept
  claims so the archive displays those dependencies faithfully.
- Removed 13 obsolete modules (7 concepts and 6 proof modules) and 101
  unused source theorem declarations. Two simplification bridges,
  `NativeMomentFamily.entries_words` and `NativeFlowCut.step_eq`, remain:
  elaboration uses them even though their proof references are erased.
- Shortened 93 qualified references using explicit `open` declarations.
  Updated descriptions to match the retained claims and removed stale
  accounts of unfinished obligations.
- `HasQPTAS` was already formalized. Its exact runtime formula now lives in
  `QPTASRuntime`; `QPTAS` focuses on the scheme predicate. The main statement
  still concludes `HasQPTAS C`.
- The proof package explicitly declares the same pinned RAM concept package
  used by its direct imports. No new external mathematical dependency.

Validation:
- `lax build --no-color --profile`: exit 0, 2m12s after the full rebuild.
  All 85 concepts and 337 proof modules compile; statement inspection passes.
- Inventory: 67 lemma concepts, 17 definitions, 1 theorem; 135 claims and
  135 proofs.
- Closure audit: zero open claims, zero claims outside headline ancestry,
  zero unmatched proofs, no admissions. Every retained claim contributes
  to the main theorem. The concept import graph has one component of size 85.
- All 663 retained concept declaration fingerprints are unchanged after
  normalizing the move of `QPTAS.timeBound` to `QPTASRuntime.timeBound`.
- `git diff --check` passes.
- 42 nonblocking Lax warnings remain: 3 proof-package dependencies and 39
  helper declarations, mostly generated structure/inductive lemmas.

Logs and audits:
- `/tmp/qptas-cleanup-lax-checked.log`
- `/tmp/qptas-cleanup-audit.json`
- `/tmp/qptas-cleanup-concept-comparison.json`
- `python3 /tmp/qptas_audit_clean.py` reproduces the graph/closure audit.
- `/tmp/QptasConceptFingerprints.lean` produces normalized fingerprints;
  the reference is `/tmp/qptas-concept-fingerprints-before.json`.

Cleanup committed and pushed as
`4f3776370f2bb234b6692c2aa7aa71b25847836d`.
`lax submit --no-color` finished with actual exit 0. Local submission build:
1m49s; independent archive validation: 31m06s; publication: 1m32s.
- Successful workflow: https://github.com/lax-archive/lax/actions/runs/38761988229
- Archive commit: `9f5b88f29f9f7b8d59b46c70cf2ef04e8a3a0783`.
- Draft: https://laxarchive.org/lax-263307/
- Issue 201 reports the immutable source accepted and the website rebuild
  event accepted. The same 42 nonblocking warnings remain.
The cleanup is complete. Registration is not requested or performed.
Later documentation-only commits do not change the validated source above.

Website deployment and live verification also succeeded:
https://github.com/lax-archive/lax-website/actions/runs/38766726169
Website tree: `9e1874fa5b73582843b7f8a128d55c067bd0dc71`.
The live page was fetched and checked after deployment: all three credits
are present, QPTASRuntime is present, the removed EntropyDecrease link is
absent, and the rendered proof network has 135 claims and 135 proofs.
There are zero local or external nodes outside the main component and
zero unknown edge endpoints. The previous page had 14 local nodes outside
that component. GitHub Pages serving propagation caused the final delay;
the live page now matches the generated revision.
Audit: `/tmp/qptas-published-audit.json`, reproduced by
`python3 /tmp/qptas_published_audit.py` after refreshing
`/tmp/qptas-published.html`. The independently checked generated page is
also recorded in `/tmp/qptas-prepared-audit.json`.

### Completed original proof and first submission

**Finished.** The headline theorem `Lax263307Proofs.MainTheorem.exists_qptas`
is proved. The public mathematical statement is unchanged.

Validation completed2026-10-15:
- Full Lean build:343 own modules; actual exit0.
- `lax build --replay --profile`: actual exit0,12m53s total.
  Strict kernel replay took11m04s. Statement inspection passed.
- Closure audit:91 concepts,166 statements,166 proofs; **zero open statements**,
  including `Lax263307.MainTheorem.exists_qptas`, using the registered external
  assumptions as the closure seed.
- Own proof source scan: no sorry/admit and no axiom declarations.
- Normal Lean root restored after Lax replay; actual exit0.

Logs: `/tmp/qptas-final-strict-replay.log`,
`/tmp/qptas-final-closure-audit.json`, `/tmp/qptas-final-root-restore.log`.
`build-output.json` records replay=true and is generated/ignored; do not force-add.
The audit can be reproduced with `/tmp/qptas-final-closure-audit.py` while that
script remains available. The source and validated proof are the durable result.

Commit d4d3b4a records the complete unweighted implementation; the final commit
adds the complete weighted Spec, all word/global-time estimates and headline
proof. No mathematical proof work remains in this submission's intended scope.
Submission requested 2026-10-15 for source commit
`9459f3f41d3ecd3bce2edd668a6a2e67d5805342`:
- Source: https://github.com/EdouardBonnet/lax-263307
- Control issue: https://github.com/lax-archive/lax/issues/201
- Validation: https://github.com/lax-archive/lax/actions/runs/38723618002
- `lax submit` completed with exit 0. Local checks, archive rebuild, and
  publication all passed; the workflow concluded successfully.
- Published draft: https://laxarchive.org/lax-263307/
- Archive commit: `b8fc370370655afebb833cad8d37d27c457d1d2b`.
- The archive rebuild took 31m48s; publication took 1m01s.
- Nonblocking warnings: 3 proof-package dependencies and 87 unused helper
  lemmas (including generated structure lemmas). No validation errors.
- Submission is a validated draft; registration was not requested or performed.
  Later documentation-only commits do not change the validated source above.
- Submission log: `/tmp/qptas-lax-submit.log`.

## Proof entry points

- MainTheorem.lean proves the single headline concept with Lax conclusion
  metadata. The public mathematical statement has not changed.
- NativeQptasImplementation.exists_fixed selects LP, flow and rounded programs,
  exact byte interfaces, semantic correctness and fixed root-budget constants
  once for the graph class. The same backends are used throughout.
- NativeWeightedExecution.command_spec proves the complete weighted source
  program from initEnv, including zero-copy inputs, and returns the functional
  weighted answer with its approximation guarantee.
- NativeQptasPositive.command_spec composes actual source reduction, blow-up,
  accuracy, budget computation, unweighted core, and owner projection/output.
- NativeQptasWordBounds discharges ALL word guards and allocation bounds.
  width = coreHost(W) + actual RootBudget.guard +100*(n+N+1)^4
  +16*(rationalBitSize+1)+100. Certificate and trajectory heights are derived
  independently of host width; rational magnitude is never used as word width.
- NativeQptasRuntime proves ordinary polynomial envelopes for width, frontend
  work and local control. NativeQptasComplexity proves the final uniform bound
  for width+layoutAllowance+10*sourceCost+1, including actual recursive work
  and the complete descending target driver.
- NativeFinalBounds absorbs the blow-up order and accuracy denominator into
  the stated inverse-accuracy/log(original-order) exponent.
- NativeQptasTransfer.qptas_of_spec uses registered lax-62 refinement codegen
  to obtain ONE fixed RAM program, for every sufficiently large word width.
- NativeUnweightedExecution.command_spec closes the full unweighted machine.
  NativeSelectedExecution.resources constructs its entire resource record;
  NativeRootWorkspace provides exact extents and stack capacity. No recursive
  callback or whole-phase execution is assumed. NativeNodeExecution.executes
  is the actual fuel induction. NativeSelectedRounds supplies every oracle
  and rounded step using the exact selected solvers.
- NativeCoreOutput proves the core emits nothing, including arbitrary virtual
  solver programs. NativeSourceFrame preserves the original input metadata,
  owner table and output buffers through saved frames and recursive execution.

## Working agreements and recovery

Keep output short; redirect compiler/replay logs to /tmp. Require actual exit0.
The user authorizes git, gh, lax and lake commands; do not ask again. Platform
sandbox requirements still apply. Do not use subagents unless requested.
No boxed mathematics. Do not claim full Sepref adoption: the proof uses
Lax62Proofs.Refine.Codegen.computesInTime_of_spec directly on structured commands.

The active mathlib build is a symlink into
/home/ebonnet/.lax/warm/v4.33.0-db584cd6d46c/.lake/packages/mathlib/.lake/build.
Do not delete it. About17GB was free at the start of final replay.

## Dependency pins

Lean4.33.0; mathlib db584cd6d46c92f209a44c0f1c829460d327499d.
- RAM808846:9394e531cc51cb67a0214bca3f9264dfe97ba5c7
- RAM–TM759944:134e398cef46599371df99f10c9007bc34ba3868
- Treewidth228581:1e200ffac8b69e63b802f0aaf1dfee79561ca39a
- Leighton–Rao455465:9988b9c5399185cfb3ca2129ca7c807fd80c2885
- Expanders920634:4e1ce662f8ff75f2fa86d3a3973c871d3068c4c0
- LP109476:0a042604c7ae1ef4cd9a4c7d82eb902f313d4864
- Refinement62:0503df0eaf4e41104b9a3aa31e3e028b5adf7a0e
- Approximation213208:180b8ec1e851a4948b7a3c77d001e29df8a32dad
- Structural560851:2748fdc0afc0b4f729b7775ca6475ba08129418a

The fixed paper snapshot is round-or-cut.pdf. Scope: Bonnet–Chang Theorem2;
applications and corollaries are outside this submission's intended proof.
