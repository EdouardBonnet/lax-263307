import Lax263307.IndependentSetEncoding
import Lax263307Proofs.NativeQptasPositive
import Lax263307Proofs.NativeFinalBounds

set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeQptasWordBounds

open Lax263307.IndependentSetEncoding

open Lax263307 GraphClasses WeightedIndependentSet
open NativeQptasImplementation NativeQptasPositive

def shape (n N : ℕ) : ℕ := 100*(n+N+1)^4

def width {C : GraphClass} (i : Fixed C) {n : ℕ} (weights : Fin n → ℚ) (ε : ℚ) : ℕ :=
  let N := order weights ε
  NativeRootWorkspace.hostHeight i.cfg (workspace i N ε)+
    NativeRootBudget.guard i.envelopeCoefficient i.envelopeExponent i.budgetCoefficient i.budgetExponent N (denominator N ε)+
    shape n N+16*NativeInputBounds.height weights ε+100

theorem shape_bound (n N : ℕ) : n*n+N*N+3*n+3*N+100 ≤ shape n N := by
  have hs : n*n+N*N+3*n+3*N+100 ≤ 100*(n+N+1)^2 := by
    nlinarith only [Nat.zero_le (n^2),Nat.zero_le (N^2),Nat.zero_le (n*N),Nat.zero_le n,Nat.zero_le N]
  exact hs.trans (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 4)))

theorem accuracy_coefficient (n N : ℕ) :
    3+8*(RecursionDepth.depth N+1)+2*N+RecursionDepth.depth N+40 ≤ shape n N := by
  have hd := RecursionDepth.logarithmic_bound N
  have hl := Nat.log2_le_self N
  have hs : n+N+1 ≤ (n+N+1)^4 := le_self_pow (by omega) (by decide)
  dsimp only [shape]
  omega

theorem basic {C : GraphClass} (i : Fixed C) {n : ℕ} (weights : Fin n → ℚ) (ε : ℚ) :
    let N := order weights ε
    let M := NativeInputBounds.magnitude weights ε
    let w := width i weights ε
    0<w ∧ 2*M^4+3<2^w ∧ n*n+3*n+3<2^w ∧ n*n+N*N+n+N+3<2^w ∧
      N*N+N+5<2^w ∧ n+N+5<2^w ∧
      3*M+8*(RecursionDepth.depth N+1)*M+2*N+RecursionDepth.depth N+40<2^w := by
  dsimp only
  let N := order weights ε
  let H := NativeInputBounds.height weights ε
  let M := NativeInputBounds.magnitude weights ε
  let w := width i weights ε
  have hH : 1 ≤ H := by dsimp only [H,NativeInputBounds.height]; omega
  have hwidth : NativeRootWorkspace.hostHeight i.cfg (workspace i N ε)+
      NativeRootBudget.guard i.envelopeCoefficient i.envelopeExponent i.budgetCoefficient i.budgetExponent N (denominator N ε)+
      shape n N+16*H+100=w := rfl
  have hs := shape_bound n N
  have hscalar : n*n+N*N+3*n+3*N+100<2^w :=
    hs.trans_lt ((by omega : shape n N ≤ w).trans_lt Nat.lt_two_pow_self)
  have hfrontend : 2*M^4+3<2^w := by
    have hv := NativeUniformWordGuards.virtual (2*H) w (by omega)
    have he : (2^H)^4=(2^(2*H))^2 := by rw [←pow_mul,←pow_mul]; congr 1; omega
    simpa only [M,NativeInputBounds.magnitude,←he] using hv
  have haccuracy : 3*M+8*(RecursionDepth.depth N+1)*M+2*N+RecursionDepth.depth N+40<2^w := by
    have hm : 1 ≤ M := NativeInputBounds.magnitude_positive weights ε
    have hc := accuracy_coefficient n N
    have hprod : 3*M+8*(RecursionDepth.depth N+1)*M+2*N+RecursionDepth.depth N+40 ≤ shape n N*M := by
      nlinarith only [hc,Nat.mul_le_mul_right M hc,hm,
        Nat.le_mul_of_pos_right (2*N+RecursionDepth.depth N+40) hm]
    have hexp : shape n N+H<w := by omega
    calc
      _ ≤ shape n N*M := hprod
      _ ≤ 2^(shape n N)*2^H := Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le
      _ = 2^(shape n N+H) := (pow_add _ _ _).symm
      _ < 2^w := Nat.pow_lt_pow_right (by decide) hexp
  change 0<w ∧ 2*M^4+3<2^w ∧ n*n+3*n+3<2^w ∧ n*n+N*N+n+N+3<2^w ∧
    N*N+N+5<2^w ∧ n+N+5<2^w ∧
    3*M+8*(RecursionDepth.depth N+1)*M+2*N+RecursionDepth.depth N+40<2^w
  exact ⟨by omega,hfrontend,by omega,by omega,by omega,by omega,haccuracy⟩

theorem input {C : GraphClass} (i : Fixed C) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (weights : Fin n → ℚ) (ε : ℚ) : ∀ z∈encodeInput G weights ε,z<2^width i weights ε := by
  intro z hz
  exact (NativeInputBounds.input_bound G weights ε z hz).trans_le
    (Nat.pow_le_pow_right (by decide) (by dsimp only [width]; omega))

theorem positive {C : GraphClass} (i : Fixed C) {n : ℕ} (weights : Fin n → ℚ) (ε : ℚ)
    (hε : 0<ε) (hε1 : ε<1) (hN : 0<order weights ε) :
    NativeQptasPositive.Bounds i n (order weights ε) (NativeInputBounds.magnitude weights ε) (width i weights ε) ε := by
  let N := order weights ε
  let D := denominator N ε
  let R := resource i N ε
  let W := workspace i N ε
  have hp := positive_parameters weights ε hN
  have hnN : n ≤ N := NativeFinalBounds.original_order_le_copy_order
    (PositiveWeights.positiveWeights weights) ε hp.1 hε hε1.le hp.2
  have hD : 4 ≤ D := (Lax263307Proofs.RecursiveAlgorithm.accuracy_budget N (ε/2) (by positivity)).1
  have hr := i.uniform N D N (by omega) hN (Nat.le_refl N)
  change ParameterResources.resource i.cfg.a i.cfg.K i.cfg.b N D ≤ R at hr
  have hNR : N ≤ R := by dsimp only [ParameterResources.resource] at hr; omega
  have hnR : n ≤ R := hnN.trans hNR
  have budget := i.budget R
  change NativeSelectedBudget.demand i.cfg i.projection i.separator i.roundedConstant R ≤ W at budget
  dsimp only [NativeSelectedBudget.demand] at budget
  have allocation : n*n+N*N+3*n+N+3 ≤ W := by
    have hn2 := Nat.mul_self_le_mul_self hnR
    have hN2 := Nat.mul_self_le_mul_self hNR
    have hs : n*n+N*N+3*n+N+3 ≤ 10*(R+1)^2 := by nlinarith only [hn2,hN2,hnR,hNR]
    have hpow := Nat.pow_le_pow_right (by omega : 1 ≤ R+1) (by decide : 2 ≤ 4)
    have hc : 10 ≤ NativeEntryResources.coefficient i.cfg := by dsimp only [NativeEntryResources.coefficient]; omega
    have he : 10*(R+1)^2 ≤ NativeEntryResources.amount i.cfg R :=
      Nat.mul_le_mul hc hpow
    exact (hs.trans he).trans (by omega)
  have hb := basic i weights ε
  refine ⟨allocation,hb.2.1,hb.2.2.1,hb.2.2.2.1,hb.2.2.2.2.1,hb.2.2.2.2.2.2,?_,?_,hb.2.2.2.2.2.1⟩
  · apply NativeUniformWordGuards.scalar
    dsimp only [width]
    omega
  · dsimp only [width]
    omega

end Lax263307Proofs.NativeQptasWordBounds
