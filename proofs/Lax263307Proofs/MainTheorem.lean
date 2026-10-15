import Lax263307.MainTheorem
import Lax263307Proofs.NativeQptasComplexity

namespace Lax263307Proofs.MainTheorem

open Lax263307 GraphClasses EdgeSublinearSeparators QPTAS WeightedIndependentSet

/--
---
conclusion: Lax263307.MainTheorem.exists_qptas
---
Select the fixed registered backends and rounded-update program once. The
complete weighted source specification is compiled through the registered
RAM refinement framework. Its checked root-resource estimates and logarithmic
recursion bound give the asserted quasipolynomial time and word width.
-/
theorem exists_qptas (C : GraphClass) (hereditary : IsHereditary C)
    (separators : HasStronglyEdgeSublinearSeparators C) : HasQPTAS C := by
  obtain ⟨i⟩ := NativeQptasImplementation.exists_fixed C hereditary separators
  obtain ⟨K,q,k,hq,hk,hbounds⟩ := NativeQptasComplexity.exists_bounds i
  let c := K*864^(i.envelopeExponent+1)+q+1
  let d := max (3*(i.envelopeExponent+1)) k
  have final (n : ℕ) (weights : Fin n → ℚ) (ε : ℚ) (hε : 0<ε) :
      NativeQptasWordBounds.width i weights ε+NativeQptasRuntime.allowance i+
        10*NativeWeightedExecution.cost i weights ε+1 ≤ timeBound c d n (rationalBitSize weights ε) ε := by
    exact (hbounds n weights ε hε).trans (NativeFinalBounds.final_time K (i.envelopeExponent+1) q k n
      (NativeQptasPositive.order weights ε) (rationalBitSize weights ε) ε hε
      (NativeQptasComplexity.copy_bound weights ε hε))
  apply NativeQptasTransfer.qptas_of_spec C (NativeWeightedExecution.command i) c d (by dsimp only [c]; omega)
    (lt_of_lt_of_le hk (Nat.le_max_right _ _))
    (fun n weights ε => NativeQptasWordBounds.width i weights ε)
    (fun n weights ε => NativeWeightedExecution.cost i weights ε)
  · intro n G _ hG weights ε hε hε1
    exact NativeQptasWordBounds.input i G weights ε
  · intro n weights ε hε hε1
    refine ⟨(NativeQptasWordBounds.basic i weights ε).1,?_⟩
    change NativeQptasWordBounds.width i weights ε+NativeQptasRuntime.allowance i ≤ _
    have h := final n weights ε hε
    omega
  · intro n weights ε hε hε1
    have h := final n weights ε hε
    omega
  · intro n G _ hG weights ε hε hε1
    exact NativeWeightedExecution.command_spec i G hG weights ε hε hε1

end Lax263307Proofs.MainTheorem
