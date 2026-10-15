import Lax263307.StrongComponentGaps
import Mathlib.Tactic

namespace Lax263307Proofs.StrongComponentGaps

open Lax263307.LinearRelaxation Lax263307.ComponentCutEncoding

theorem coordinate_indicator_sum {n r : ℕ} (S : Finset (Fin n)) :
    (∑ B : Coordinate n r, if S = B.val then (1 : ℝ) else 0) ≤ 1 := by
  classical
  by_cases hS : S.card ≤ r + 2
  · let B₀ : Coordinate n r := ⟨S, hS⟩
    have heq (B : Coordinate n r) : S = B.val ↔ B₀ = B := by
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    simp_rw [heq]
    simp
  · have hne (B : Coordinate n r) : S ≠ B.val := by intro h; exact hS (h ▸ B.property)
    simp [hne]

/--
---
conclusion: Lax263307.StrongComponentGaps.coefficient_l1
---
Sum the absolute integer coefficients. Repeated coordinates only decrease the bound.
-/
theorem coefficient_l1 {n r : ℕ} (A C : Finset (Fin n)) (u : ℕ) :
    (∑ B : Coordinate n r, |(coefficient A C u B : ℝ)|) ≤ C.card + u := by
  classical
  have hpoint (B : Coordinate n r) : |(coefficient A C u B : ℝ)| ≤
      (∑ v ∈ C, if insert v A = B.val then (1 : ℝ) else 0) +
        (if A = B.val then (u : ℝ) else 0) := by
    unfold coefficient
    push_cast
    have h := abs_sub_le (∑ v ∈ C, if insert v A = B.val then (1 : ℝ) else 0)
      0 (if A = B.val then (u : ℝ) else 0)
    have hsum : 0 ≤ (∑ v ∈ C, if insert v A = B.val then (1 : ℝ) else 0) :=
      Finset.sum_nonneg (fun v _ => by split_ifs <;> positivity)
    have hif : 0 ≤ (if A = B.val then (u : ℝ) else 0) := by split_ifs <;> positivity
    simpa only [sub_zero, zero_sub, abs_neg, abs_of_nonneg hsum, abs_of_nonneg hif] using h
  calc
    _ ≤ ∑ B : Coordinate n r, ((∑ v ∈ C, if insert v A = B.val then (1 : ℝ) else 0) +
        (if A = B.val then (u : ℝ) else 0)) := Finset.sum_le_sum (fun B _ => hpoint B)
    _ = (∑ v ∈ C, ∑ B : Coordinate n r, if insert v A = B.val then (1 : ℝ) else 0) +
        (∑ B : Coordinate n r, if A = B.val then (u : ℝ) else 0) := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
    _ ≤ C.card + u := by
      have hC : (∑ v ∈ C, ∑ B : Coordinate n r, if insert v A = B.val then (1 : ℝ) else 0) ≤ C.card := by
        simpa using Finset.sum_le_sum (fun v (_ : v ∈ C) => coordinate_indicator_sum (insert v A))
      have hu : (∑ B : Coordinate n r, if A = B.val then (u : ℝ) else 0) ≤ u := by
        have h := mul_le_mul_of_nonneg_left (coordinate_indicator_sum (r := r) A) (Nat.cast_nonneg u : (0 : ℝ) ≤ _)
        simpa only [Finset.mul_sum, mul_ite, mul_one, mul_zero] using h
      exact add_le_add hC hu

/--
---
conclusion: Lax263307.StrongComponentGaps.evaluation_stable
---
Apply the triangle inequality and the coefficient sum bound to coordinate errors.
-/
theorem evaluation_stable {n r : ℕ} (A C : Finset (Fin n)) (u : ℕ)
    (x y : MomentVector n r) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (near : ∀ B, |x B - y B| ≤ ρ) :
    |evaluate (coefficient A C u) x - evaluate (coefficient A C u) y| ≤ (C.card + u) * ρ := by
  classical
  unfold evaluate
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ B, |(coefficient A C u B : ℝ) * x B - (coefficient A C u B : ℝ) * y B| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ B, |(coefficient A C u B : ℝ)| * ρ := by
      apply Finset.sum_le_sum
      intro B _
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left (near B) (abs_nonneg _)
    _ ≤ _ := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (coefficient_l1 A C u) hρ

/--
---
conclusion: Lax263307.StrongComponentGaps.component_gap
---
Multiply the heavy-part rounded cost gap by the positive conditioning moment. The independence bound makes the cut valid on the exact hull.
-/
theorem component_gap {n r : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ)
    (y : MomentVector n r) (A C : Finset (Fin n)) (u : ℕ)
    (size : A.card ≤ r) (bound : IsIndependenceBound G C u)
    (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) (hn : 0 < n) (hk : 0 < k)
    (moment : η ≤ value y A)
    (heavy : δ * (k : ℝ) / (2 * n) ≤ ∑ v ∈ C, conditioned y A v)
    (rounded : (u : ℝ) ≤ (1 - δ) * ∑ v ∈ C, conditioned y A v) :
    (∀ z ∈ independentSetHull G k r, evaluate (coefficient A C u) z ≤ 0) ∧
      η * δ ^ 2 * (k : ℝ) / (2 * n) ≤ evaluate (coefficient A C u) y := by
  have hpos : 0 < value y A := hη.trans_le moment
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  let c := ∑ v ∈ C, conditioned y A v
  have hcost : δ ^ 2 * (k : ℝ) / (2 * n) ≤ c - u := by
    have hmul := mul_le_mul_of_nonneg_left heavy hδ.le
    have he : δ * (δ * (k : ℝ) / (2 * n)) = δ ^ 2 * (k : ℝ) / (2 * n) := by ring
    rw [he] at hmul
    dsimp only [c]
    nlinarith [hmul]
  have hgap : 0 ≤ δ ^ 2 * (k : ℝ) / (2 * n) := by positivity
  have heq : evaluate (coefficient A C u) y = value y A * (c - u) := by
    rw [Lax263307.ComponentCutEncoding.evaluation_identity A C u size]
    dsimp [c]
    simp_rw [conditioned, ← Finset.sum_div]
    field_simp
  refine ⟨?_, ?_⟩
  · intro z hz
    rw [Lax263307.ComponentCutEncoding.evaluation_identity A C u size]
    exact sub_nonpos.mpr (Lax263307.ComponentCuts.valid_cut G k r C u bound A size z hz)
  · rw [heq]
    have h := mul_le_mul moment hcost hgap hpos.le
    calc
      _ = η * (δ ^ 2 * (k : ℝ) / (2 * n)) := by ring
      _ ≤ _ := h


/--
---
conclusion: Lax263307.StrongComponentGaps.query_gap
---
Subtract the maximal coordinate perturbation loss from the feasible query gap, using k≥1 and coefficient sum at most 2n.
-/
theorem query_gap {n r : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ)
    (x y : MomentVector n r) (A C : Finset (Fin n)) (u : ℕ)
    (size : A.card ≤ r) (bound : IsIndependenceBound G C u) (upper : u ≤ n)
    (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) (hn : 0 < n) (hk : 0 < k)
    (moment : η ≤ value y A)
    (heavy : δ * (k : ℝ) / (2 * n) ≤ ∑ v ∈ C, conditioned y A v)
    (rounded : (u : ℝ) ≤ (1 - δ) * ∑ v ∈ C, conditioned y A v)
    (near : ∀ B, |x B - y B| ≤ η * δ ^ 2 / (8 * (n : ℝ) ^ 2)) :
    (∀ z ∈ independentSetHull G k r, evaluate (coefficient A C u) z ≤ 0) ∧
      η * δ ^ 2 / (4 * n) ≤ evaluate (coefficient A C u) x := by
  obtain ⟨hvalid, hgap⟩ := Lax263307.StrongComponentGaps.component_gap G k y A C u size bound η δ hη hδ hn hk moment heavy rounded
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  let ρ := η * δ ^ 2 / (8 * (n : ℝ) ^ 2)
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hstab := Lax263307.StrongComponentGaps.evaluation_stable A C u x y ρ hρ near
  have hC : (C.card : ℝ) ≤ n := by exact_mod_cast C.card_le_univ.trans_eq (Fintype.card_fin n)
  have hu : (u : ℝ) ≤ n := by exact_mod_cast upper
  have hstab' : |evaluate (coefficient A C u) x - evaluate (coefficient A C u) y| ≤ 2 * n * ρ :=
    hstab.trans (mul_le_mul_of_nonneg_right (by linarith : (C.card : ℝ) + u ≤ 2 * n) hρ)
  have hsmall : 2 * (n : ℝ) * ρ = η * δ ^ 2 / (4 * n) := by dsimp [ρ]; field_simp; ring
  have hbase : η * δ ^ 2 / (2 * n) ≤ η * δ ^ 2 * (k : ℝ) / (2 * n) :=
    div_le_div_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_left hk1 (show 0 ≤ η * δ ^ 2 by positivity)]) (by positivity)
  have heq : η * δ ^ 2 / (2 * n) = 2 * (η * δ ^ 2 / (4 * n)) := by ring
  have hdiff := (abs_le.mp hstab').1
  rw [hsmall] at hdiff
  rw [heq] at hbase
  exact ⟨hvalid, by linarith⟩


end Lax263307Proofs.StrongComponentGaps
