import Lax263307.NearOracle
import Lax263307Proofs.RationalConditioning
import Mathlib.Tactic

namespace Lax263307Proofs.NearOracle

open scoped NNRat
open Lax263307.NearOracle Lax263307.GraphClasses Lax263307.PowerBagBounds
open Lax263307.LinearRelaxation Lax263307.RationalConditioning
open Lax263307.AlgorithmParameters Lax263307.ComputedSeparators
open Lax263307.RepeatedCutAccounting

theorem costs_cast {n r : ℕ} (y : RationalVector n r) (A : Finset (Fin n))
    (nonnegative : ∀ v, 0 ≤ conditioned (realVector y) A v) (v : Fin n) :
    (costs y A v : ℝ) = conditioned (realVector y) A v := by
  have heq : ((rationalValue y (insert v A) / rationalValue y A : ℚ) : ℝ) =
      conditioned (realVector y) A v := by
    simp only [conditioned, Lax263307Proofs.RationalConditioning.value_cast, Rat.cast_div]
  have hq : (0 : ℚ) ≤ rationalValue y (insert v A) / rationalValue y A := by
    exact_mod_cast (heq.symm ▸ nonnegative v)
  change ((max 0 (rationalValue y (insert v A) / rationalValue y A) : ℚ) : ℝ) = _
  rw [max_eq_right hq]
  exact heq

theorem order_complete (q : ℕ) (i : Option (Fin q)) : i ∈ order q := by
  cases i <;> simp [order]

/-- The selected backend's separator guarantee, retained for actual
recursive child-domain and resource proofs. -/
def SeparatorCorrect (C : GraphClass) (flow : List ℕ → List ℕ) (a K B : ℕ) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G ∈ C n → 0 < n → ∀ (x : Fin n → ℚ≥0) (k p ℓ : ℕ),
      0 < k → 0 < p → 0 < ℓ →
      (∀ v, (x v : ℝ) ≤ 1) → (∑ v, (x v : ℝ)) ≤ k →
      Lax263307.Entropy.edgeCost G (fun v => (x v : ℝ)) ≤ (k : ℝ) ^ 2 / p →
      (K : ℝ) * ((ℓ : ℝ) + 1) ^ (4 * a + 2) ≤ k →
      (2 * K : ℝ) * ((ℓ : ℝ) + 1) ^ (4 * a + 2) ≤ p →
      let cs := cuts (step flow G x B ℓ k) n Finset.univ
      cs.length ≤ n ∧
        Lax263307.EdgeSublinearSeparators.IsBalancedSeparator G
          (Lax263307.ComputedSeparators.separator cs) ∧
        cost (fun v => (x v : ℝ)) (Lax263307.ComputedSeparators.separator cs) ≤
          12 * (ratio B n : ℝ) * k / ℓ ∧
        ∃ P : Lax263307.SeparatorComponents.Partition G
            (Lax263307.ComputedSeparators.separator cs) (Option (Fin cs.length)),
          (∀ i, P.vertices i = pieces cs i) ∧ ∀ i, 3 * (P.vertices i).card ≤ 2 * n

theorem exists_oracle_with_parts (C : GraphClass) (hereditary : IsHereditary C)
    (a A : ℕ) (ha : 0 < a) (hA : 0 < A) (class_bound : HasPowerBagBound C a A) :
    ∃ (flow : List ℕ → List ℕ) (K B : ℕ), Lax759944.RamPolytime.RamPolytime flow ∧
      0 < K ∧ 0 < B ∧ SeparatorCorrect C flow a K B ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G ∈ C n → 0 < n → ∀ (D k h : ℕ), 4 ≤ D → cutoff a K B n D < k →
      ∀ (y : RationalVector n (level a K B n D)),
      IsFeasible G k (level a K B n D) (realVector y) →
      ∀ (x : MomentVector n (level a K B n D)),
      (∀ T, |x T - realVector y T| ≤ (momentFloor a K B n D : ℝ) *
        (1 / (D : ℝ)) ^ 2 / (32 * (n : ℝ) ^ 2)) →
      ∀ (child : Finset (Fin n) → ℕ → Option (Finset (Fin n))), ChildCorrect G D h child →
      Correct G k h D (momentFloor a K B n D) x (run flow a K B D G k y child) := by
  obtain ⟨flow, K, B, hpoly, hK, hB, hsep⟩ :=
    Lax263307.ComputedSeparators.light_separator C hereditary a A ha hA class_bound
  refine ⟨flow, K, B, hpoly, hK, hB, hsep, ?_⟩
  intro n G _ hG hn D k h hD hlarge y hfeasible x hnear child hchild
  let r := level a K B n D
  let p := sparsity a K B n D
  let ℓ := load B n D
  let δ : ℚ := 1 / D
  let η : ℝ := momentFloor a K B n D
  have hb := budgets hK hB hD hlarge
  have hk : 0 < k := by omega
  have hδcast : (δ : ℝ) = 1 / (D : ℝ) := by dsimp [δ]; push_cast; rfl
  have hδ : (0 : ℚ) < δ := by rw [← Rat.cast_pos (K := ℝ), hδcast]; exact hb.2.2.2.1
  have hsmall : δ ≤ (1 / 4 : ℚ) := by
    have hh : (δ : ℝ) ≤ ((1 / 4 : ℚ) : ℝ) := by
      norm_num
      rw [hδcast]
      exact hb.2.2.2.2.1
    exact Rat.cast_le.mp hh
  have hη : 0 < η := by
    have hp : 0 < sparsity a K B n D := hb.2.1
    dsimp only [η]
    rw [conditioning_floor]
    unfold Lax263307.HeavyConditioning.probabilityFloor
    positivity
  obtain ⟨A, hfind, hsize, hmoment, hpositive, hcosts, hmass, hedge⟩ :=
    Lax263307.HeavyRationalConditioning.search_correct G k r p y hfeasible hn hk hb.2.2.1 hb.2.1 hb.2.2.2.2.2.2.1
  have hmoment' : η ≤ value (realVector y) A := by
    dsimp only [η]
    rw [conditioning_floor]
    exact hmoment
  let costs' := costs y A
  have hcast (v : Fin n) : (costs' v : ℝ) = conditioned (realVector y) A v :=
    costs_cast y A (fun v => (hcosts v).1) v
  have hbound (v : Fin n) : (costs' v : ℝ) ≤ 1 := by rw [hcast]; exact (hcosts v).2
  have hmass' : (∑ v, (costs' v : ℝ)) ≤ k := by simp only [hcast]; exact hmass.le
  have hedge' : Lax263307.Entropy.edgeCost G (fun v => (costs' v : ℝ)) ≤ (k : ℝ) ^ 2 / p := by
    simpa only [hcast] using hedge
  have hS := hsep n G hG hn costs' k p ℓ hk hb.2.1 hb.1 hbound hmass' hedge'
    hb.2.2.2.2.2.2.2.1 hb.2.2.2.2.2.2.2.2
  let cs := cuts (step flow G costs' B ℓ k) n Finset.univ
  obtain ⟨hq, _, hlight, P, hverts, hparts⟩ := hS
  have hverts' : P.vertices = pieces cs := funext hverts
  let c : Option (Fin cs.length) → ℚ := fun i => ∑ v ∈ pieces cs i, (costs' v : ℚ)
  have hc (i : Option (Fin cs.length)) : (c i : ℝ) = ∑ v ∈ P.vertices i, conditioned (realVector y) A v := by
    dsimp only [c]
    rw [hverts i]
    push_cast
    apply Finset.sum_congr rfl
    intro v _
    exact hcast v
  have hcount : Fintype.card (Option (Fin cs.length)) ≤ 2 * n := by
    change cs.length ≤ n at hq
    simp only [Fintype.card_option, Fintype.card_fin]
    omega
  have hlight' : (∑ v ∈ Lax263307.ComputedSeparators.separator cs, conditioned (realVector y) A v) ≤
      (δ : ℝ) * k := by
    have hℓ : (0 : ℝ) < ℓ := by exact_mod_cast hb.1
    have hbudget : 12 * (ratio B n : ℝ) ≤ (δ : ℝ) * ℓ := by
      dsimp only [ratio]
      push_cast
      rw [hδcast]
      simpa only [mul_assoc] using hb.2.2.2.2.2.1
    have hlast : 12 * (ratio B n : ℝ) * k / ℓ ≤ (δ : ℝ) * k := by
      apply (div_le_iff₀ hℓ).mpr
      nlinarith only [mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg k)]
    have hh := hlight.trans hlast
    simpa only [cost, hcast] using hh
  have hqueries : ∀ i : Option (Fin cs.length), δ * k / (4 * n) < c i →
      match child (P.vertices i) (Lax263307.ComputedRounding.target δ (c i)) with
      | some I => I ⊆ P.vertices i ∧ G.IsIndepSet (I : Set (Fin n)) ∧
          (1 - 4 * (δ : ℝ)) ^ h * (Lax263307.ComputedRounding.target δ (c i) : ℝ) ≤ I.card
      | none => IsIndependenceBound G (P.vertices i) (Lax263307.ComputedRounding.target δ (c i) - 1) := by
    intro i _
    have hh := hchild (P.vertices i) (hparts i) (Lax263307.ComputedRounding.target δ (c i))
    cases he : child (P.vertices i) (Lax263307.ComputedRounding.target δ (c i)) <;>
      simpa only [he, hδcast] using hh
  have hnear' : ∀ T, |x T - realVector y T| ≤ η * (δ : ℝ) ^ 2 / (32 * (n : ℝ) ^ 2) := by
    simpa only [hδcast] using hnear
  have hcol := Lax263307.ComputedRounding.collect_correct G k h δ η hn hk hδ hsmall hη
    x (realVector y) hfeasible A (Lax263307.ComputedSeparators.separator cs) P hsize hmoment' hcount hlight'
    (order cs.length) (order_complete cs.length) c hc
    (fun i t => child (P.vertices i) t) hqueries hnear'
  rw [hverts'] at hcol
  dsimp only [run]
  rw [hfind]
  change Correct G k h D η x
    (match Lax263307.ComputedRounding.collect (order cs.length) (pieces cs) δ k c
      (fun i t => child (pieces cs i) t) with
      | .found I => Result.found I
      | .cut C u => Result.cut A C u)
  cases hout : Lax263307.ComputedRounding.collect (order cs.length) (pieces cs) δ k c
      (fun i t => child (pieces cs i) t) with
  | found I =>
    rw [hout] at hcol
    simpa only [Correct, hδcast] using hcol
  | cut C u =>
    rw [hout] at hcol
    change A.card ≤ r ∧ _
    exact ⟨hsize, by simpa only [hδcast] using hcol⟩


end Lax263307Proofs.NearOracle
