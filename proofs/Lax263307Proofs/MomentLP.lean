import Lax263307.MomentLP
import Lax263307.ComponentCutEncoding
import Mathlib.Tactic

namespace Lax263307Proofs.MomentLP

open Lax263307.LinearRelaxation Lax263307.CoordinateCatalog Lax263307.MomentLP
open Lax109476.LinearProgram Lax109476.RationalCertificates

/--
---
conclusion: Lax263307.MomentLP.decode_encode
---
The computable catalog equivalence and its inverse cancel on each coordinate.
-/
theorem decode_encode {K : Type} {n r : ℕ} (y : Coordinate n r → K) : decode (encode y) = y := by
  funext A
  simp [decode, encode]


/--
---
conclusion: Lax263307.MomentLP.single_row_value
---
Inside the coordinate domain, a singleton row selects the unique native index of that coordinate. Outside the domain every coefficient is zero.
-/
theorem single_row_value {n r : ℕ} (x : Index n r → ℝ) (A : Finset (Fin n)) :
    (∑ j, (singleRow A j : ℝ) * x j) = value (decode x) A := by
  by_cases hA : A.card ≤ r + 2
  · let B : Coordinate n r := ⟨A, hA⟩
    let i : Index n r := (indexing n r).symm B
    have heq (j : Index n r) : A = (indexing n r j).val ↔ i = j := by
      constructor
      · intro h
        apply (indexing n r).injective
        change indexing n r ((indexing n r).symm B) = indexing n r j
        rw [Equiv.apply_symm_apply]
        exact Subtype.ext h
      · intro h
        rw [← h]
        simp [i, B]
    simp only [singleRow, apply_ite, Rat.cast_one, Rat.cast_zero, ite_mul, one_mul, zero_mul]
    simp_rw [heq]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp [value, decode, hA, i, B]
  · have hne (j : Index n r) : A ≠ (indexing n r j).val := by
      intro h
      exact hA (h ▸ (indexing n r j).property)
    simp [singleRow, hne, value, hA]

theorem monotone_row_value {n r : ℕ} (x : Index n r → ℝ) (A : Finset (Fin n)) (v : Fin n) :
    (∑ j, (monotoneRow A v j : ℝ) * x j) = value (decode x) (insert v A) - value (decode x) A := by
  simp only [monotoneRow, Rat.cast_sub, sub_mul, Finset.sum_sub_distrib]
  rw [Lax263307.MomentLP.single_row_value, Lax263307.MomentLP.single_row_value]

theorem mass_row_value {n r : ℕ} (x : Index n r → ℝ) (A : Finset (Fin n)) (k : ℕ) :
    (∑ j, (massRow A k j : ℝ) * x j) =
      (∑ v, value (decode x) (insert v A)) - (k : ℝ) * value (decode x) A := by
  simp only [massRow, Rat.cast_sub, Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast,
    sub_mul, Finset.sum_sub_distrib]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [Lax263307.MomentLP.single_row_value]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, Lax263307.MomentLP.single_row_value]


abbrev Rows (n r : ℕ) := Fin (2 + (dimension n r + (dimension n r + (dimension n r * n + (dimension n r + dimension n r)))))

def normalPort {n r : ℕ} (i : Fin 2) : Rows n r :=
  Fin.castAdd (dimension n r + (dimension n r + (dimension n r * n + (dimension n r + dimension n r)))) i

def upperPort {n r : ℕ} (i : Index n r) : Rows n r :=
  Fin.natAdd 2 (Fin.castAdd (dimension n r + (dimension n r * n + (dimension n r + dimension n r))) i)

def vanishPort {n r : ℕ} (i : Index n r) : Rows n r :=
  Fin.natAdd 2 (Fin.natAdd (dimension n r) (Fin.castAdd (dimension n r * n + (dimension n r + dimension n r)) i))

def monotonePort {n r : ℕ} (i : Index n r) (v : Fin n) : Rows n r :=
  Fin.natAdd 2 (Fin.natAdd (dimension n r) (Fin.natAdd (dimension n r)
    (Fin.castAdd (dimension n r + dimension n r) (finProdFinEquiv (i, v)))))

def massPlusPort {n r : ℕ} (i : Index n r) : Rows n r :=
  Fin.natAdd 2 (Fin.natAdd (dimension n r) (Fin.natAdd (dimension n r)
    (Fin.natAdd (dimension n r * n) (Fin.castAdd (dimension n r) i))))

def massMinusPort {n r : ℕ} (i : Index n r) : Rows n r :=
  Fin.natAdd 2 (Fin.natAdd (dimension n r) (Fin.natAdd (dimension n r)
    (Fin.natAdd (dimension n r * n) (Fin.natAdd (dimension n r) i))))

theorem indexed_value {n r : ℕ} (x : Index n r → ℝ) (i : Index n r) :
    value (decode x) (indexing n r i).val = x i := by
  rw [value, dif_pos (indexing n r i).property]
  change x ((indexing n r).symm (indexing n r i)) = x i
  rw [Equiv.symm_apply_apply]

theorem normal_row {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ)
    (x : Index n r → ℝ) (i : Fin 2) :
    rowValue (toReal (program G k r)) x (normalPort i) =
      if i = 0 then value (decode x) ∅ else -value (decode x) ∅ := by
  unfold rowValue toReal program normalPort
  simp only [Fin.addCases_left]
  by_cases hi : i = 0
  · simp only [if_pos hi]
    exact Lax263307.MomentLP.single_row_value x ∅
  · simp only [if_neg hi, Rat.cast_neg, neg_mul, Finset.sum_neg_distrib]
    rw [Lax263307.MomentLP.single_row_value]

theorem upper_row {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ)
    (x : Index n r → ℝ) (i : Index n r) :
    rowValue (toReal (program G k r)) x (upperPort i) = x i := by
  unfold rowValue toReal program upperPort
  simp only [Fin.addCases_left, Fin.addCases_right]
  rw [Lax263307.MomentLP.single_row_value, indexed_value]

theorem vanish_row {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ)
    (x : Index n r → ℝ) (i : Index n r) :
    rowValue (toReal (program G k r)) x (vanishPort i) =
      if G.IsIndepSet ((indexing n r i).val : Set (Fin n)) then 0 else x i := by
  unfold rowValue toReal program vanishPort
  simp only [Fin.addCases_left, Fin.addCases_right]
  split_ifs
  · simp
  · rw [Lax263307.MomentLP.single_row_value, indexed_value]

theorem monotone_row {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ)
    (x : Index n r → ℝ) (i : Index n r) (v : Fin n) :
    rowValue (toReal (program G k r)) x (monotonePort i v) =
      if (indexing n r i).val.card ≤ r + 1 then
        value (decode x) (insert v (indexing n r i).val) - value (decode x) (indexing n r i).val else 0 := by
  unfold rowValue toReal program monotonePort
  simp only [Fin.addCases_left, Fin.addCases_right, Equiv.symm_apply_apply]
  split_ifs
  · exact monotone_row_value x _ v
  · simp

theorem mass_plus_row {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ)
    (x : Index n r → ℝ) (i : Index n r) :
    rowValue (toReal (program G k r)) x (massPlusPort i) =
      if (indexing n r i).val.card ≤ r + 1 then
        (∑ v, value (decode x) (insert v (indexing n r i).val)) - (k : ℝ) * value (decode x) (indexing n r i).val else 0 := by
  unfold rowValue toReal program massPlusPort
  simp only [Fin.addCases_left, Fin.addCases_right]
  split_ifs
  · exact mass_row_value x _ k
  · simp

theorem mass_minus_row {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ)
    (x : Index n r → ℝ) (i : Index n r) :
    rowValue (toReal (program G k r)) x (massMinusPort i) =
      if (indexing n r i).val.card ≤ r + 1 then
        -((∑ v, value (decode x) (insert v (indexing n r i).val)) - (k : ℝ) * value (decode x) (indexing n r i).val) else 0 := by
  unfold rowValue toReal program massMinusPort
  simp only [Fin.addCases_right]
  split_ifs
  · simp only [Rat.cast_neg, neg_mul, Finset.sum_neg_distrib]
    rw [mass_row_value]
  · simp


theorem normal_rhs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ) (i : Fin 2) :
    (toReal (program G k r)).b (normalPort i) = if i = 0 then 1 else -1 := by
  by_cases hi : i = 0 <;> simp [toReal, program, normalPort, hi]

theorem upper_rhs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ) (i : Index n r) :
    (toReal (program G k r)).b (upperPort i) = 1 := by
  simp only [toReal, program, upperPort, Fin.addCases_left, Fin.addCases_right, Rat.cast_one]

theorem vanish_rhs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ) (i : Index n r) :
    (toReal (program G k r)).b (vanishPort i) = 0 := by
  simp only [toReal, program, vanishPort, Fin.addCases_right, Rat.cast_zero]

theorem monotone_rhs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ) (i : Index n r) (v : Fin n) :
    (toReal (program G k r)).b (monotonePort i v) = 0 := by
  simp only [toReal, program, monotonePort, Fin.addCases_right, Rat.cast_zero]

theorem mass_plus_rhs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ) (i : Index n r) :
    (toReal (program G k r)).b (massPlusPort i) = 0 := by
  simp only [toReal, program, massPlusPort, Fin.addCases_right, Rat.cast_zero]

theorem mass_minus_rhs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ) (i : Index n r) :
    (toReal (program G k r)).b (massMinusPort i) = 0 := by
  simp only [toReal, program, massMinusPort, Fin.addCases_right, Rat.cast_zero]

/--
---
conclusion: Lax263307.MomentLP.primal_characterization
---
Expand each explicit row family. Paired rows give the normalization and mass equalities; upper and nonindependence rows complement primal nonnegativity, and active insertion rows give monotonicity.
-/
theorem primal_characterization {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ)
    (x : Index n r → ℝ) :
    PrimalFeasible (toReal (program G k r)) x ↔ Lax263307.LinearRelaxation.IsFeasible G k r (decode x) := by
  constructor
  · rintro ⟨hnonnegative, hrows⟩
    have hupper (i : Index n r) : x i ≤ 1 := by
      have h := hrows (upperPort i)
      rwa [upper_row, upper_rhs] at h
    exact {
      normalized := by
        have h0 := hrows (normalPort (0 : Fin 2))
        have h1 := hrows (normalPort (1 : Fin 2))
        rw [normal_row, normal_rhs] at h0 h1
        norm_num at h0 h1
        linarith
      bounds := fun A => ⟨hnonnegative ((indexing n r).symm A), hupper ((indexing n r).symm A)⟩
      monotone := by
        intro A hA v
        let B : Coordinate n r := ⟨A, by omega⟩
        let i : Index n r := (indexing n r).symm B
        have hi : (indexing n r i).val = A := by simp [i, B]
        have h := hrows (monotonePort i v)
        rw [monotone_row, monotone_rhs, hi, if_pos hA] at h
        exact sub_nonpos.mp h
      vanishes := by
        intro A hA
        let i : Index n r := (indexing n r).symm A
        have hi : indexing n r i = A := Equiv.apply_symm_apply _ _
        have h := hrows (vanishPort i)
        rw [vanish_row, vanish_rhs, hi, if_neg hA] at h
        exact le_antisymm h (hnonnegative i)
      mass := by
        intro A hA
        let B : Coordinate n r := ⟨A, by omega⟩
        let i : Index n r := (indexing n r).symm B
        have hi : (indexing n r i).val = A := by simp [i, B]
        have hp := hrows (massPlusPort i)
        have hm := hrows (massMinusPort i)
        rw [mass_plus_row, mass_plus_rhs, hi, if_pos hA] at hp
        rw [mass_minus_row, mass_minus_rhs, hi, if_pos hA] at hm
        linarith }
  · intro feasible
    refine ⟨?_, ?_⟩
    · intro i
      simpa [decode] using (feasible.bounds (indexing n r i)).1
    · intro row
      refine Fin.addCases (fun i : Fin 2 => ?_) (fun row => ?_) row
      · change rowValue (toReal (program G k r)) x (normalPort i) ≤ (toReal (program G k r)).b (normalPort i)
        rw [normal_row, normal_rhs, feasible.normalized]
      · refine Fin.addCases (fun i : Index n r => ?_) (fun row => ?_) row
        · change rowValue (toReal (program G k r)) x (upperPort i) ≤ (toReal (program G k r)).b (upperPort i)
          rw [upper_row, upper_rhs]
          simpa [decode] using (feasible.bounds (indexing n r i)).2
        · refine Fin.addCases (fun i : Index n r => ?_) (fun row => ?_) row
          · change rowValue (toReal (program G k r)) x (vanishPort i) ≤ (toReal (program G k r)).b (vanishPort i)
            rw [vanish_row, vanish_rhs]
            by_cases hI : G.IsIndepSet ((indexing n r i).val : Set (Fin n))
            · simp [hI]
            · have hzero : x i = 0 := by simpa [decode] using feasible.vanishes (indexing n r i) hI
              simp [hI, hzero]
          · refine Fin.addCases (fun j : Fin (dimension n r * n) => ?_) (fun row => ?_) row
            · obtain ⟨⟨i, v⟩, rfl⟩ := (finProdFinEquiv : Index n r × Fin n ≃ Fin (dimension n r * n)).surjective j
              change rowValue (toReal (program G k r)) x (monotonePort i v) ≤ (toReal (program G k r)).b (monotonePort i v)
              rw [monotone_row, monotone_rhs]
              by_cases hi : (indexing n r i).val.card ≤ r + 1
              · rw [if_pos hi]
                exact sub_nonpos.mpr (feasible.monotone _ hi v)
              · simp [hi]
            · refine Fin.addCases (fun i : Index n r => ?_) (fun i : Index n r => ?_) row
              · change rowValue (toReal (program G k r)) x (massPlusPort i) ≤ (toReal (program G k r)).b (massPlusPort i)
                rw [mass_plus_row, mass_plus_rhs]
                by_cases hi : (indexing n r i).val.card ≤ r + 1
                · rw [if_pos hi, feasible.mass _ hi]
                  simp
                · simp [hi]
              · change rowValue (toReal (program G k r)) x (massMinusPort i) ≤ (toReal (program G k r)).b (massMinusPort i)
                rw [mass_minus_row, mass_minus_rhs]
                by_cases hi : (indexing n r i).val.card ≤ r + 1
                · rw [if_pos hi, feasible.mass _ hi]
                  simp
                · simp [hi]


/--
---
conclusion: Lax263307.MomentLP.evaluate_encoding
---
Reindex the finite sum through the computable catalog equivalence to identify a component-cut evaluation with the native dot product.
-/
theorem evaluate_encoding {n r : ℕ} (a : Coordinate n r → ℤ) (x : Index n r → ℝ) :
    Lax263307.ComponentCutEncoding.evaluate a (decode x) =
      (fun j => ((encode a j : ℤ) : ℝ)) ⬝ᵥ x := by
  classical
  unfold Lax263307.ComponentCutEncoding.evaluate dotProduct
  have h := (indexing n r).sum_comp (fun A => (a A : ℝ) * decode x A)
  simpa only [decode, encode, Equiv.symm_apply_apply] using h.symm

end Lax263307Proofs.MomentLP
