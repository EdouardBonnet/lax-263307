import Lax263307.DistanceProjection
import Mathlib.Tactic

namespace Lax263307Proofs.DistanceProjection

open Lax109476.LinearProgram Lax263307.DistanceProjection

theorem old_row {m n : ℕ} (P : Program ℝ m n) (center : Fin n → ℝ)
    (z : Fin (n + 1) → ℝ) (i : Fin m) :
    rowValue (distanceProgram P center) z (Fin.castAdd (n + n) i) = rowValue P (point z) i := by
  unfold rowValue distanceProgram
  simp only [Fin.addCases_left]
  rw [Fin.sum_univ_add]
  simp [point]

theorem plus_row {m n : ℕ} (P : Program ℝ m n) (center : Fin n → ℝ)
    (z : Fin (n + 1) → ℝ) (i : Fin n) :
    rowValue (distanceProgram P center) z (Fin.natAdd m (Fin.castAdd n i)) = point z i - distance z := by
  unfold rowValue distanceProgram
  simp only [Fin.addCases_left, Fin.addCases_right]
  rw [Fin.sum_univ_add]
  simp [point, distance, sub_eq_add_neg]

theorem minus_row {m n : ℕ} (P : Program ℝ m n) (center : Fin n → ℝ)
    (z : Fin (n + 1) → ℝ) (i : Fin n) :
    rowValue (distanceProgram P center) z (Fin.natAdd m (Fin.natAdd n i)) = -point z i - distance z := by
  unfold rowValue distanceProgram
  simp only [Fin.addCases_right]
  rw [Fin.sum_univ_add]
  simp [point, distance, sub_eq_add_neg]


/--
---
conclusion: Lax263307.DistanceProjection.primal_characterization
---
Expand the appended rows and split finite indices. The two distance inequalities are exactly the coordinate absolute-value bounds.
-/
theorem primal_characterization {m n : ℕ} (P : Program ℝ m n) (center : Fin n → ℝ)
    (z : Fin (n + 1) → ℝ) :
    PrimalFeasible (distanceProgram P center) z ↔
      PrimalFeasible P (point z) ∧ 0 ≤ distance z ∧
        ∀ j, |point z j - center j| ≤ distance z := by
  constructor
  · rintro ⟨hnonneg, hrows⟩
    refine ⟨⟨fun j => hnonneg (Fin.castAdd 1 j), fun i => ?_⟩,
      hnonneg (Fin.natAdd n (0 : Fin 1)), fun j => ?_⟩
    · have h := hrows (Fin.castAdd (n + n) i)
      rw [old_row] at h
      simpa only [distanceProgram, Fin.addCases_left] using h
    · have hplus := hrows (Fin.natAdd m (Fin.castAdd n j))
      have hminus := hrows (Fin.natAdd m (Fin.natAdd n j))
      rw [plus_row] at hplus
      rw [minus_row] at hminus
      simp only [distanceProgram, Fin.addCases_left, Fin.addCases_right] at hplus hminus
      exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rintro ⟨⟨hnonneg, hrows⟩, ht, hnear⟩
    constructor
    · intro j
      refine Fin.addCases (fun j => hnonneg j) (fun j => ?_) j
      have hj : j = 0 := Fin.eq_zero j
      subst j
      exact ht
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · rw [old_row]
        simpa only [distanceProgram, Fin.addCases_left] using hrows i
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · rw [plus_row]
          simp only [distanceProgram, Fin.addCases_left, Fin.addCases_right]
          have h := (abs_le.mp (hnear j)).2
          linarith
        · rw [minus_row]
          simp only [distanceProgram, Fin.addCases_right]
          have h := (abs_le.mp (hnear j)).1
          linarith

theorem objective_value {m n : ℕ} (P : Program ℝ m n) (center : Fin n → ℝ)
    (z : Fin (n + 1) → ℝ) :
    primalValue (distanceProgram P center) z = -distance z := by
  unfold primalValue distanceProgram
  rw [Fin.sum_univ_add]
  simp [distance]

/--
---
conclusion: Lax263307.DistanceProjection.objective_bounded
---
The objective equals the negative of the nonnegative distance variable, hence is at most zero.
-/
theorem objective_bounded {m n : ℕ} (P : Program ℝ m n) (center : Fin n → ℝ) :
    IsBoundedAbove (distanceProgram P center) := by
  refine ⟨0, fun z hz => ?_⟩
  rw [objective_value]
  exact neg_nonpos.mpr ((primal_characterization P center z).mp hz).2.1


/--
---
conclusion: Lax263307.DistanceProjection.projection_feasible_iff
---
Every projected primal point gives an original feasible point. Conversely append the sum of coordinate absolute differences as a feasible distance bound.
-/
theorem projection_feasible_iff {m n : ℕ} (P : Program ℝ m n) (center : Fin n → ℝ) :
    IsFeasible (distanceProgram P center) ↔ IsFeasible P := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨point z, ((primal_characterization P center z).mp hz).1⟩
  · rintro ⟨y, hy⟩
    let t := ∑ j, |y j - center j|
    let z : Fin (n + 1) → ℝ := Fin.addCases y (fun _ : Fin 1 => t)
    refine ⟨z, (primal_characterization P center z).mpr ?_⟩
    have hpoint : point z = y := by funext j; simp [point, z]
    have hdist : distance z = t := by simp [distance, z]
    rw [hpoint, hdist]
    refine ⟨hy, Finset.sum_nonneg (fun j _ => abs_nonneg _), ?_⟩
    intro j
    exact Finset.single_le_sum (fun j _ => abs_nonneg (y j - center j)) (Finset.mem_univ j)

theorem point_column {m n : ℕ} (P : Program ℝ m n) (center : Fin n → ℝ)
    (dual : Fin (m + (n + n)) → ℝ) (j : Fin n) :
    columnValue (distanceProgram P center) dual (Fin.castAdd 1 j) =
      columnValue P (oldMultipliers dual) j - normal dual j := by
  unfold columnValue distanceProgram
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right]
  simp [oldMultipliers, plusMultipliers, minusMultipliers, normal]
  ring

theorem distance_column {m n : ℕ} (P : Program ℝ m n) (center : Fin n → ℝ)
    (dual : Fin (m + (n + n)) → ℝ) :
    columnValue (distanceProgram P center) dual (Fin.natAdd n (0 : Fin 1)) =
      -(∑ j, plusMultipliers dual j) - ∑ j, minusMultipliers dual j := by
  unfold columnValue distanceProgram
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right]
  simp [plusMultipliers, minusMultipliers, Finset.sum_neg_distrib]
  ring

theorem dual_objective {m n : ℕ} (P : Program ℝ m n) (center : Fin n → ℝ)
    (dual : Fin (m + (n + n)) → ℝ) :
    dualValue (distanceProgram P center) dual = dualValue P (oldMultipliers dual) - ∑ j, normal dual j * center j := by
  unfold dualValue distanceProgram
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right, neg_mul, Finset.sum_neg_distrib]
  simp only [oldMultipliers, normal, minusMultipliers, plusMultipliers, sub_mul, Finset.sum_sub_distrib]
  have hcomm : (∑ j, center j * dual (Fin.natAdd m (Fin.castAdd n j))) =
      ∑ j, dual (Fin.natAdd m (Fin.castAdd n j)) * center j := by apply Finset.sum_congr rfl; intro j _; ring
  have hcomm' : (∑ j, center j * dual (Fin.natAdd m (Fin.natAdd n j))) =
      ∑ j, dual (Fin.natAdd m (Fin.natAdd n j)) * center j := by apply Finset.sum_congr rfl; intro j _; ring
  rw [hcomm, hcomm']
  ring


/--
---
conclusion: Lax263307.DistanceProjection.dual_normal
---
The distance column bounds the sum of the two nonnegative multiplier families by one. Their difference is therefore bounded in L1, and the original columns and rows make it valid on every feasible point.
-/
theorem dual_normal {m n : ℕ} (P : Program ℝ m n) (center : Fin n → ℝ)
    (dual : Fin (m + (n + n)) → ℝ) (feasible : DualFeasible (distanceProgram P center) dual) :
    (∑ j, |normal dual j|) ≤ 1 ∧
      ∀ z, PrimalFeasible P z → (∑ j, normal dual j * z j) ≤ dualValue P (oldMultipliers dual) := by
  have hplus (j : Fin n) : 0 ≤ plusMultipliers dual j := feasible.1 _
  have hminus (j : Fin n) : 0 ≤ minusMultipliers dual j := feasible.1 _
  have hmass : (∑ j, plusMultipliers dual j) + (∑ j, minusMultipliers dual j) ≤ 1 := by
    have h := feasible.2 (Fin.natAdd n (0 : Fin 1))
    rw [distance_column] at h
    simp only [distanceProgram, Fin.addCases_right] at h
    linarith
  constructor
  · have h := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
      show |normal dual j| ≤ plusMultipliers dual j + minusMultipliers dual j from by
        unfold normal
        exact abs_le.mpr ⟨by linarith [hplus j, hminus j], by linarith [hplus j, hminus j]⟩)
    rw [Finset.sum_add_distrib] at h
    exact h.trans hmass
  · intro z hz
    have hcol (j : Fin n) : normal dual j ≤ columnValue P (oldMultipliers dual) j := by
      have h := feasible.2 (Fin.castAdd 1 j)
      rw [point_column] at h
      simp only [distanceProgram, Fin.addCases_left] at h
      linarith
    calc
      _ ≤ ∑ j, columnValue P (oldMultipliers dual) j * z j :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hcol j) (hz.1 j))
      _ = ∑ i, oldMultipliers dual i * rowValue P z i := by
        unfold columnValue rowValue
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ dualValue P (oldMultipliers dual) :=
        Finset.sum_le_sum (fun i _ => by
          have hnonnegative : 0 ≤ oldMultipliers dual i := feasible.1 _
          simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hz.2 i) hnonnegative)

/--
---
conclusion: Lax263307.DistanceProjection.optimal_gap
---
Combine primal characterization with the dual normal bounds. Matching objectives identify the separation gap at the center with the returned distance.
-/
theorem optimal_gap {m n : ℕ} (P : Program ℝ m n) (center : Fin n → ℝ)
    (z : Fin (n + 1) → ℝ) (dual : Fin (m + (n + n)) → ℝ)
    (primal : PrimalFeasible (distanceProgram P center) z)
    (dual_feasible : DualFeasible (distanceProgram P center) dual)
    (matching : primalValue (distanceProgram P center) z = dualValue (distanceProgram P center) dual) :
    PrimalFeasible P (point z) ∧ 0 ≤ distance z ∧
      (∀ j, |point z j - center j| ≤ distance z) ∧
      (∑ j, |normal dual j|) ≤ 1 ∧
      (∀ y, PrimalFeasible P y → (∑ j, normal dual j * y j) ≤ dualValue P (oldMultipliers dual)) ∧
      (∑ j, normal dual j * center j) - dualValue P (oldMultipliers dual) = distance z := by
  obtain ⟨hpoint, hdist, hnear⟩ := (primal_characterization P center z).mp primal
  obtain ⟨hl1, hvalid⟩ := Lax263307.DistanceProjection.dual_normal P center dual dual_feasible
  refine ⟨hpoint, hdist, hnear, hl1, hvalid, ?_⟩
  rw [objective_value, dual_objective] at matching
  linarith


end Lax263307Proofs.DistanceProjection
