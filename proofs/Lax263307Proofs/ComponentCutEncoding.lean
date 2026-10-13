import Lax263307.ComponentCutEncoding
import Lax263307Proofs.RelaxationAlgebra

namespace Lax263307Proofs.ComponentCutEncoding

open Lax263307.LinearRelaxation Lax263307.ComponentCutEncoding

theorem coordinate_sum {n r : ℕ} (A : Finset (Fin n)) (size : A.card ≤ r + 2)
    (z : MomentVector n r) :
    (∑ B : Coordinate n r, if A = B.val then z B else 0) = value z A := by
  classical
  rw [RelaxationAlgebra.value_of_size z A size]
  rw [Finset.sum_eq_single ⟨A, size⟩]
  · simp
  · intro B _ hB
    have hne : A ≠ B.val := fun he => hB (Subtype.ext he.symm)
    simp [hne]
  · simp

/--
---
conclusion: Lax263307.ComponentCutEncoding.evaluation_identity
---
Interchange the two finite sums. The coefficient for each inserted set
selects precisely its coordinate; the final term selects the coordinate of
the conditioning set.
-/
theorem evaluation_identity {n r : ℕ} (A C : Finset (Fin n)) (u : ℕ)
    (size : A.card ≤ r) (z : MomentVector n r) :
    evaluate (coefficient A C u) z =
      (∑ v ∈ C, value z (insert v A)) - (u : ℝ) * value z A := by
  classical
  unfold evaluate coefficient
  push_cast
  simp_rw [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
  have hfirst : (∑ B : Coordinate n r, ∑ v ∈ C,
      (if insert v A = B.val then (1 : ℝ) else 0) * z B) =
      ∑ v ∈ C, value z (insert v A) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    simpa only [ite_mul, one_mul, zero_mul] using
      coordinate_sum (insert v A) (by have := Finset.card_insert_le v A; omega) z
  have hsecond : (∑ B : Coordinate n r,
      (if A = B.val then (u : ℝ) else 0) * z B) =
      (u : ℝ) * value z A := by
    simp only [ite_mul, zero_mul]
    have heq (B : Coordinate n r) : (if A = B.val then (u : ℝ) * z B else 0) =
        (u : ℝ) * (if A = B.val then z B else 0) := by split_ifs <;> simp
    simp_rw [heq, ← Finset.mul_sum]
    rw [coordinate_sum A (by omega)]
  rw [hfirst, hsecond]

/--
---
conclusion: Lax263307.ComponentCutEncoding.coefficient_bound
---
The positive contribution counts at most `|C| ≤ n` terms, each equal to one.
The negative contribution is either zero or `u ≤ n`. Their difference lies
between `-n` and `n`, even when inserted coordinates repeat.
-/
theorem coefficient_bound {n r : ℕ} (A C : Finset (Fin n)) (u : ℕ)
    (bound : u ≤ n) (B : Coordinate n r) :
    |coefficient A C u B| ≤ (n : ℤ) := by
  have hsum₀ : (0 : ℤ) ≤ ∑ v ∈ C, if insert v A = B.val then 1 else 0 := by
    apply Finset.sum_nonneg
    intro v _
    split_ifs <;> norm_num
  have hsum₁ : (∑ v ∈ C, if insert v A = B.val then (1 : ℤ) else 0) ≤ n := by
    calc
      (∑ v ∈ C, if insert v A = B.val then (1 : ℤ) else 0) ≤ ∑ _v ∈ C, (1 : ℤ) := by
        apply Finset.sum_le_sum
        intro v _
        split_ifs <;> norm_num
      _ = (C.card : ℤ) := by simp
      _ ≤ n := by exact_mod_cast (show C.card ≤ n by simpa using Finset.card_le_univ C)
  have hu : (u : ℤ) ≤ n := by exact_mod_cast bound
  rw [coefficient, abs_le]
  split_ifs <;> constructor <;> omega

end Lax263307Proofs.ComponentCutEncoding
