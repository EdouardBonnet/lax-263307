import Lax263307Proofs.NativeQptasWordBounds

namespace Lax263307Proofs.NativeWeightedExecution

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 GraphClasses WeightedIndependentSet
open NativeQptasImplementation

def command {C : GraphClass} (i : Fixed C) : Com :=
  NativeQptasProgram.command i.cfg i.envelopeCoefficient i.envelopeExponent i.budgetCoefficient i.budgetExponent

def cost {C : GraphClass} (i : Fixed C) {n : ℕ} (weights : Fin n → ℚ) (ε : ℚ) : ℕ :=
  NativeQptasPositive.cost i n (NativeQptasPositive.order weights ε) ε

def zeroExtent (n : ℕ) (a : String) : ℕ := if a="weighted.output" then n else n*n+3*n+3

/-- The complete weighted native command has the exact functional answer,
with all execution, allocation and word guards proved. Only the final global
quasipolynomial comparison is separate. -/
theorem command_spec {C : GraphClass} (i : Fixed C) {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : G∈C n) (weights : Fin n → ℚ) (ε : ℚ) (hε : 0<ε) (hε1 : ε<1) :
    ∃ (I : Finset (Fin n)) (ext : String → ℕ),IsApproximation G weights ε I ∧
      Spec (2^NativeQptasWordBounds.width i weights ε)
        (fun σ => σ=initEnv ext (encodeInput G weights ε)) (command i)
        (fun _ τ => τ.out=encodeOutput I) (cost i weights ε) := by
  let N := NativeQptasPositive.order weights ε
  let M := NativeInputBounds.magnitude weights ε
  let w := NativeQptasWordBounds.width i weights ε
  let I := WeightedAlgorithm.solve i.lp i.flow i.cfg.a i.cfg.K i.cfg.b G weights ε
  have hM := NativeInputBounds.magnitude_positive weights ε
  have hnM := (NativeInputBounds.order_bound weights ε).le
  have hw := NativeInputBounds.weight_bounds weights ε
  have hεM := NativeInputBounds.accuracy_bounds weights ε
  have hb := NativeQptasWordBounds.basic i weights ε
  have hinitial (ext : String → ℕ) : NativeStateBounds.Bounded (2^w) (initEnv ext (encodeInput G weights ε)) :=
    NativeStateBounds.initial ext (Nat.two_pow_pos w) (NativeQptasWordBounds.input i G weights ε)
  have lengths (ext : String → ℕ) (a : String) :
      ((initEnv ext (encodeInput G weights ε)).arrs a).length=ext a := List.length_replicate
  by_cases hz : N=0
  · let ext := zeroExtent n
    refine ⟨I,ext,i.semantic n G hG weights ε hε hε1,?_⟩
    intro σ hσ
    subst σ
    have zero := NativeQptasZero.command_spec (2^w) M hM hnM i.cfg i.envelopeCoefficient i.envelopeExponent
      i.budgetCoefficient i.budgetExponent i.lp i.flow G weights ε hε hw hεM hb.2.1 hb.2.2.1 hz
    obtain ⟨τ,rr,out⟩ := zero (initEnv ext (encodeInput G weights ε))
      ⟨rfl,by rw [lengths]; simp [ext,zeroExtent],by rw [lengths]; simp [ext,zeroExtent]; omega,
        by rw [lengths]; simp [ext,zeroExtent]⟩
    refine ⟨τ,rr.mono ?_,?_⟩
    · change NativeBlowUp.cost n 0+24*n+20 ≤ cost i weights ε
      change NativeBlowUp.cost n 0+24*n+20 ≤ NativeQptasPositive.cost i n N ε
      rw [hz]
      dsimp only [NativeQptasPositive.cost]
      omega
    · simpa only [initEnv,List.nil_append] using out
  · have hN : 0<N := by omega
    let W := NativeQptasPositive.workspace i N ε
    let ext := NativeRootWorkspace.extent i.cfg N W n
    refine ⟨I,ext,i.semantic n G hG weights ε hε hε1,?_⟩
    intro σ hσ
    subst σ
    obtain ⟨τ,rr,out⟩ := NativeQptasPositive.command_spec i G hG weights ε hε M w hM hnM hw hεM hN
      (NativeQptasWordBounds.positive i weights ε hε hε1 hN) (initEnv ext (encodeInput G weights ε))
      ⟨rfl,hinitial ext,lengths ext⟩
    exact ⟨τ,rr,by simpa only [initEnv,List.nil_append] using out⟩

end Lax263307Proofs.NativeWeightedExecution
