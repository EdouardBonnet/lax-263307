import Lax263307.IndependentSetEncoding
import Lax263307Proofs.NativeWeightedExecution

set_option maxHeartbeats 500000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeQptasRuntime

open Lax263307.IndependentSetEncoding

open Lax263307 GraphClasses AlgorithmParameters WeightedIndependentSet
open NativeQptasImplementation NativeQptasPositive NativePolynomialEnvelope

def workspaceAt {C : GraphClass} (i : Fixed C) (R : ℕ) : ℕ := i.budgetCoefficient*(R+1)^i.budgetExponent

def budgetBound {C : GraphClass} (i : Fixed C) (R : ℕ) : ℕ :=
  i.envelopeCoefficient+i.envelopeExponent+i.budgetCoefficient+i.budgetExponent+
    2*R+R+R+R+R+R+R+(R+1)^i.budgetExponent+workspaceAt i R+2*(workspaceAt i R+1)+100

def widthBound {C : GraphClass} (i : Fixed C) (J : ℕ) : ℕ :=
  NativeRootWorkspace.hostHeight i.cfg (workspaceAt i J)+budgetBound i J+
    100*(2*J+1)^4+16*(J+1)+100

def frontendBound {C : GraphClass} (i : Fixed C) (J : ℕ) : ℕ :=
  NativeBlowUp.cost J J+(16*(J*J)+14)+18+(14*(2*J+2)+28)+
    (48*J+12*i.envelopeExponent+12*i.budgetExponent+78)+(24*J+44*J+36)+20

def allowance {C : GraphClass} (i : Fixed C) : ℕ :=
  Lax455465Proofs.RamTransfer.layoutAllowance
    (Lax455465Proofs.RamAutomaticLayout.layout (NativeWeightedExecution.command i))

theorem polynomial {C : GraphClass} (i : Fixed C) :
    Bounded (fun J => widthBound i J+allowance i+10*frontendBound i J+1) := by
  simp only [widthBound,budgetBound,workspaceAt,frontendBound,NativeBlowUp.cost,
    NativeRootWorkspace.hostHeight,NativeNearResources.wordHeight,NativeRootWorkspace.frameLength,
    NativeRootWorkspace.stride,NativeRoundedResources.wordHeight]
  polynomial_envelope

theorem local_polynomial {C : GraphClass} (i : Fixed C) :
    Bounded (fun R => NativeLocalTime.steps (workspaceAt i R)+NativeLocalTime.branches (workspaceAt i R)+
      NativeLocalTime.time i.cfg (workspaceAt i R) (2*(workspaceAt i R+1))) := by
  obtain ⟨P,hP⟩ := NativeLocalTime.polynomial i.cfg
  apply NativePolynomialEnvelope.of_le (eval P (show Bounded (workspaceAt i) from by
    change Bounded (fun R => workspaceAt i R)
    simp only [workspaceAt]
    polynomial_envelope))
  exact fun R => hP (workspaceAt i R)

theorem host_mono (cfg : NativeCoreMachine.Config) {W V : ℕ} (h : W ≤ V) :
    NativeRootWorkspace.hostHeight cfg W ≤ NativeRootWorkspace.hostHeight cfg V := by
  dsimp only [NativeRootWorkspace.hostHeight,NativeNearResources.wordHeight,NativeRootWorkspace.frameLength,
    NativeRootWorkspace.stride,NativeRoundedResources.wordHeight]
  gcongr

theorem budget_mono {C : GraphClass} (i : Fixed C) {R J : ℕ} (h : R ≤ J) : budgetBound i R ≤ budgetBound i J := by
  dsimp only [budgetBound,workspaceAt]
  gcongr

theorem parameters {C : GraphClass} (i : Fixed C) (N : ℕ) (ε : ℚ) (hε : 0<ε) :
    let D := denominator N ε
    let X := D*logarithm N
    let R := resource i N ε
    0<D ∧ 1 ≤ X ∧ N ≤ R ∧ D ≤ R ∧ logarithm N ≤ R ∧ X ≤ R ∧
      X^i.envelopeExponent ≤ R ∧ i.envelopeCoefficient*X^i.envelopeExponent ≤ R := by
  dsimp only
  let D := denominator N ε
  let X := D*logarithm N
  let R := resource i N ε
  have hD : 0<D := lt_of_lt_of_le (by decide : 0<4)
    (Lax263307Proofs.RecursiveAlgorithm.accuracy_budget N (ε/2) (by positivity)).1
  have hL : 1 ≤ logarithm N := by dsimp only [logarithm]; omega
  have hX : 1 ≤ X := Nat.mul_pos hD hL
  have hH : i.envelopeCoefficient*X^i.envelopeExponent ≤ R := Nat.lt_two_pow_self.le
  have hP : X^i.envelopeExponent ≤ R :=
    (Nat.le_mul_of_pos_left _ i.envelopeCoefficientPositive).trans hH
  have hXR : X ≤ R := (le_self_pow hX (Nat.ne_of_gt i.envelopeExponentPositive)).trans hP
  have hNR : N ≤ R := by
    by_cases hn : 0<N
    · have h := i.uniform N D N hD hn (Nat.le_refl N)
      change ParameterResources.resource i.cfg.a i.cfg.K i.cfg.b N D ≤ R at h
      dsimp only [ParameterResources.resource] at h
      omega
    · omega
  have hDR : D ≤ R := (Nat.le_mul_of_pos_right _ hL).trans hXR
  have hLR : logarithm N ≤ R := (Nat.le_mul_of_pos_left _ hD).trans hXR
  exact ⟨hD,hX,hNR,hDR,hLR,hXR,hP,hH⟩

theorem budget_guard {C : GraphClass} (i : Fixed C) (N : ℕ) (ε : ℚ) (hε : 0<ε) :
    NativeRootBudget.guard i.envelopeCoefficient i.envelopeExponent i.budgetCoefficient i.budgetExponent
      N (denominator N ε) ≤ budgetBound i (resource i N ε) := by
  have hp := parameters i N ε hε
  dsimp only [NativeRootBudget.guard,NativeRootResource.budget,budgetBound,workspaceAt]
  gcongr
  all_goals first | exact Nat.le_refl _ | exact hp.2.2.1 | exact hp.2.2.2.1 | exact hp.2.2.2.2.1 |
    exact hp.2.2.2.2.2.1 | exact hp.2.2.2.2.2.2.1 | exact hp.2.2.2.2.2.2.2

theorem width_bound {C : GraphClass} (i : Fixed C) {n : ℕ} (weights : Fin n → ℚ) (ε : ℚ) (hε : 0<ε) :
    NativeQptasWordBounds.width i weights ε ≤ widthBound i (max (resource i (order weights ε) ε) (rationalBitSize weights ε)) := by
  let N := order weights ε
  let R := resource i N ε
  let ℓ := rationalBitSize weights ε
  let J := max R ℓ
  have hR : R ≤ J := Nat.le_max_left _ _
  have hℓ : ℓ ≤ J := Nat.le_max_right _ _
  have hn : n ≤ J := (NativeInputBounds.order_le_bits weights ε).trans hℓ
  have hN : N ≤ J := (parameters i N ε hε).2.2.1.trans hR
  have hW : workspace i N ε ≤ workspaceAt i J := by
    change workspaceAt i R ≤ workspaceAt i J
    dsimp only [workspaceAt]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hR 1) _)
  have hh := host_mono i.cfg hW
  have hb := (budget_guard i N ε hε).trans (budget_mono i hR)
  have hs : NativeQptasWordBounds.shape n N ≤ 100*(2*J+1)^4 := by
    dsimp only [NativeQptasWordBounds.shape]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  change _ ≤ widthBound i J
  dsimp only [NativeQptasWordBounds.width,widthBound]
  have hheight : NativeInputBounds.height weights ε ≤ J+1 := by dsimp only [NativeInputBounds.height]; omega
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hh hb) hs)
    (Nat.mul_le_mul_left 16 hheight)) 100

theorem frontend_bound {C : GraphClass} (i : Fixed C) {n : ℕ} (weights : Fin n → ℚ) (ε : ℚ) (hε : 0<ε) :
    NativeWeightedExecution.cost i weights ε ≤ NativeUnweightedExecution.cost i.cfg (order weights ε) (workspace i (order weights ε) ε)+
      frontendBound i (max (resource i (order weights ε) ε) (rationalBitSize weights ε)) := by
  let N := order weights ε
  let R := resource i N ε
  let J := max R (rationalBitSize weights ε)
  have hp := parameters i N ε hε
  have hR : R ≤ J := Nat.le_max_left _ _
  have hn : n ≤ J := (NativeInputBounds.order_le_bits weights ε).trans (Nat.le_max_right _ _)
  have hN : N ≤ J := hp.2.2.1.trans hR
  have hblowup : NativeBlowUp.cost n N ≤ NativeBlowUp.cost J J := by
    dsimp only [NativeBlowUp.cost]; gcongr
  have hbudget : budgetCost i N ε ≤ 48*J+12*i.envelopeExponent+12*i.budgetExponent+78 := by
    have hs : N.size ≤ N := Nat.size_le.mpr Nat.lt_two_pow_self
    have ht : (2*N).size ≤ 2*N := Nat.size_le.mpr Nat.lt_two_pow_self
    have hexp : i.envelopeCoefficient*(denominator N ε*logarithm N)^i.envelopeExponent ≤ J := hp.2.2.2.2.2.2.2.trans hR
    dsimp only [budgetCost]
    omega
  have hdepth : RecursionDepth.depth N ≤ 2*J+2 := by
    have h := RecursionDepth.logarithmic_bound N
    have hl := Nat.log2_le_self N
    omega
  have hNN : N*N ≤ J*J := Nat.mul_self_le_mul_self hN
  change NativeQptasPositive.cost i n N ε ≤ NativeUnweightedExecution.cost i.cfg N (workspace i N ε)+frontendBound i J
  dsimp only [NativeQptasPositive.cost,frontendBound]
  omega

end Lax263307Proofs.NativeQptasRuntime
