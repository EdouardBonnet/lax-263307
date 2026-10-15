# QPTAS proof handoff

Updated 2026-10-15. Read this first when resuming. WORKPLAN.txt keeps the
chronological history, including earlier incomplete checkpoints.

## Current status

### Draft cleanup completed locally (2026-10-15)

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

Next: commit, push, and update the existing Lax draft; archive validation
and publication are pending. Registration is not requested.

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
Lax62Proofs.Refine.Codegen.solves_of_spec for the final code-generation descent.

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

The fixed paper snapshot is round-or-cut.pdf. Scope: Bonnet–Chang Theorem2;
applications and corollaries are outside this submission's intended proof.
