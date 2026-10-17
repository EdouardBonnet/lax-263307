import Lax263307.IndependentSetEncoding
import Lax263307Proofs.NativeQptasRuntime

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeQptasComplexity

open Lax263307.IndependentSetEncoding

open Lax263307 GraphClasses AlgorithmParameters WeightedIndependentSet
open NativeQptasImplementation NativeQptasPositive NativeQptasRuntime

theorem exponent_mono (A d e n D : ℕ) (hD : 0<D) (hde : d ≤ e) :
    NativeRootResource.envelope A d n D ≤ NativeRootResource.envelope A e n D := by
  have hX : 1 ≤ D*logarithm n := Nat.mul_pos hD (by dsimp only [logarithm]; omega)
  exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX hde))

theorem scale (A d n D q : ℕ) (hD : 0<D) :
    q*NativeRootResource.envelope A d n D ≤ NativeRootResource.envelope (A+q) d n D := by
  let T := (D*logarithm n)^d
  have hT : 1 ≤ T := Nat.one_le_pow _ _ (Nat.mul_pos hD (by dsimp only [logarithm]; omega))
  calc
    _ ≤ 2^q*2^(A*T) := Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le
    _ = 2^(q+A*T) := (pow_add _ _ _).symm
    _ ≤ 2^((A+q)*T) := Nat.pow_le_pow_right (by decide) (by nlinarith only [Nat.mul_le_mul_left q hT])

theorem add (A B d n D : ℕ) (hD : 0<D) :
    NativeRootResource.envelope A d n D+NativeRootResource.envelope B d n D ≤
      NativeRootResource.envelope (A+B+1) d n D := by
  let T := (D*logarithm n)^d
  have hT : 1 ≤ T := Nat.one_le_pow _ _ (Nat.mul_pos hD (by dsimp only [logarithm]; omega))
  have hA : 2^(A*T) ≤ 2^((A+B)*T) := Nat.pow_le_pow_right (by decide) (by nlinarith only [])
  have hB : 2^(B*T) ≤ 2^((A+B)*T) := Nat.pow_le_pow_right (by decide) (by nlinarith only [])
  calc
    _ ≤ 2^((A+B)*T)+2^((A+B)*T) := Nat.add_le_add hA hB
    _ = 2^((A+B)*T+1) := by rw [pow_succ]; omega
    _ ≤ 2^((A+B+1)*T) := Nat.pow_le_pow_right (by decide) (by nlinarith only [hT])

theorem core_bound {C : GraphClass} (i : Fixed C) :
    ∃ K : ℕ,∀ N ε,0<ε → NativeUnweightedExecution.cost i.cfg N (workspace i N ε) ≤
      NativeRootResource.envelope K (i.envelopeExponent+1) N (denominator N ε) := by
  obtain ⟨B,f,hB,hf,hbound⟩ := NativePolynomialEnvelope.monomial (local_polynomial i)
  let A := 3*(B+f*(i.envelopeCoefficient+1)+1)
  refine ⟨A+i.envelopeCoefficient+9,?_⟩
  intro N ε hε
  let D := denominator N ε
  let X := D*logarithm N
  let R := resource i N ε
  let W := workspace i N ε
  let U := NativeRootResource.envelope A (i.envelopeExponent+1) N D
  have hp := parameters i N ε hε
  have hD : 0<D := hp.1
  have hR : 1 ≤ R := Nat.one_le_two_pow
  have hU : 1 ≤ U := Nat.one_le_two_pow
  have caps := hbound R
  change NativeLocalTime.steps W+NativeLocalTime.branches W+NativeLocalTime.time i.cfg W (2*(W+1)) ≤ B*(R+1)^f at caps
  let NS := NativeRecursionBudget.work (NativeLocalTime.steps W) (NativeLocalTime.branches W) (RecursionDepth.depth N)
  let NT := NativeRecursionBudget.work (NativeLocalTime.time i.cfg W (2*(W+1))) (NativeLocalTime.branches W) (RecursionDepth.depth N)
  have hs : NS ≤ U := NativeRootResource.recursive_bound B f i.envelopeCoefficient i.envelopeExponent N D
    (NativeLocalTime.steps W) (NativeLocalTime.branches W) hD (by exact (by omega : NativeLocalTime.steps W ≤ B*(R+1)^f))
    (by exact (by omega : NativeLocalTime.branches W ≤ B*(R+1)^f))
  have ht : NT ≤ U := NativeRootResource.recursive_bound B f i.envelopeCoefficient i.envelopeExponent N D
    (NativeLocalTime.time i.cfg W (2*(W+1))) (NativeLocalTime.branches W) hD
    (by exact (by omega : NativeLocalTime.time i.cfg W (2*(W+1)) ≤ B*(R+1)^f))
    (by exact (by omega : NativeLocalTime.branches W ≤ B*(R+1)^f))
  have hlocal : NativeUnweightedExecution.cost i.cfg N W ≤ 397*U*R := by
    change (NT+26+68*(NS+3))*N+98 ≤ _
    have hnR : N ≤ R := hp.2.2.1
    have htimes : (NT+26+68*(NS+3))*N ≤ 299*U*R :=
      Nat.mul_le_mul (by nlinarith only [hs,ht,hU]) hnR
    have hUR : 1 ≤ U*R := Nat.mul_pos hU hR
    nlinarith only [htimes,Nat.mul_le_mul_left 98 hUR]
  have hRR : R ≤ NativeRootResource.envelope i.envelopeCoefficient (i.envelopeExponent+1) N D :=
    exponent_mono _ _ _ _ _ hD (by omega)
  have hT : 1 ≤ X^(i.envelopeExponent+1) := Nat.one_le_pow _ _ hp.2.1
  calc
    NativeUnweightedExecution.cost i.cfg N W ≤ 397*U*R := hlocal
    _ ≤ 2^9*2^(A*X^(i.envelopeExponent+1))*2^(i.envelopeCoefficient*X^(i.envelopeExponent+1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ (by decide : 397 ≤ 2^9)) hRR
    _ = 2^(9+A*X^(i.envelopeExponent+1)+i.envelopeCoefficient*X^(i.envelopeExponent+1)) := by rw [←pow_add,←pow_add]
    _ ≤ 2^((A+i.envelopeCoefficient+9)*X^(i.envelopeExponent+1)) :=
      Nat.pow_le_pow_right (by decide) (by nlinarith only [Nat.mul_le_mul_left 9 hT])

/-- One fixed global estimate pays both the compiled command's word layout
and its complete time, with polynomial dependence on rational input bits. -/
theorem exists_bounds {C : GraphClass} (i : Fixed C) :
    ∃ K q k : ℕ,0<q ∧ 0<k ∧ ∀ n (weights : Fin n → ℚ) ε,0<ε →
      NativeQptasWordBounds.width i weights ε+allowance i+10*NativeWeightedExecution.cost i weights ε+1 ≤
        NativeRootResource.envelope K (i.envelopeExponent+1) (order weights ε) (denominator (order weights ε) ε)+
          q*(rationalBitSize weights ε+1)^k := by
  obtain ⟨q,k,hq,hk,hpoly⟩ := NativePolynomialEnvelope.monomial (polynomial i)
  obtain ⟨A,hcore⟩ := core_bound i
  let B := q+k*(i.envelopeCoefficient+1)
  refine ⟨A+10+B+1,q,k,hq,hk,?_⟩
  intro n weights ε hε
  let N := order weights ε
  let D := denominator N ε
  let R := resource i N ε
  let ℓ := rationalBitSize weights ε
  let J := max R ℓ
  have hD : 0<D := (parameters i N ε hε).1
  have hw := width_bound i weights ε hε
  have ht := frontend_bound i weights ε hε
  change NativeQptasWordBounds.width i weights ε ≤ widthBound i J at hw
  change NativeWeightedExecution.cost i weights ε ≤ NativeUnweightedExecution.cost i.cfg N (workspace i N ε)+frontendBound i J at ht
  have hp := hpoly J
  have hjoint : NativeQptasWordBounds.width i weights ε+allowance i+10*NativeWeightedExecution.cost i weights ε+1 ≤
      10*NativeUnweightedExecution.cost i.cfg N (workspace i N ε)+q*(J+1)^k := by omega
  have hsplit : q*(J+1)^k ≤ q*(R+1)^k+q*(ℓ+1)^k := by
    change q*(max R ℓ+1)^k ≤ _
    by_cases h : R ≤ ℓ
    · rw [max_eq_right h]; omega
    · rw [max_eq_left (by omega : ℓ ≤ R)]; omega
  have hc := scale A (i.envelopeExponent+1) N D 10 hD
  have hcoreScaled := (Nat.mul_le_mul_left 10 (hcore N ε hε)).trans hc
  have hbudget : q*(R+1)^k ≤ NativeRootResource.envelope B i.envelopeExponent N D :=
    NativeRootResource.budget_bound q k i.envelopeCoefficient i.envelopeExponent N D hD
  have hb := hbudget.trans (exponent_mono B i.envelopeExponent (i.envelopeExponent+1) N D hD (by omega))
  have hsum := add (A+10) B (i.envelopeExponent+1) N D hD
  have he := (Nat.add_le_add hcoreScaled hb).trans hsum
  change NativeQptasWordBounds.width i weights ε+allowance i+10*NativeWeightedExecution.cost i weights ε+1 ≤
    NativeRootResource.envelope (A+10+B+1) (i.envelopeExponent+1) N D+q*(ℓ+1)^k
  omega

theorem copy_bound {n : ℕ} (weights : Fin n → ℚ) (ε : ℚ) (hε : 0<ε) :
    order weights ε ≤ 2*n^2*⌈ε⁻¹⌉₊ := by
  by_cases hz : order weights ε=0
  · omega
  · have hp := positive_parameters weights ε (by omega)
    exact NativeFinalBounds.copy_order (PositiveWeights.positiveWeights weights) ε
      (fun v => le_max_right _ _) hp.1 hε hp.2

end Lax263307Proofs.NativeQptasComplexity
