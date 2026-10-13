import Lax263307.MomentLP
import Lax263307.HeavyConditioning
import Lax263307.RoundedOracleSearch
import Mathlib.Data.Nat.Log

/-!
---
title: Explicit integer budgets for the round-or-cut algorithm
type: theorem
---
Fixed class constants and an integer accuracy denominator determine the
load, edge sparsity, conditioning level, and small-target cutoff.
The conditioning moment floor supplies a uniform protected radius.
A larger integer precision budget makes that dyadic radius small enough
using only natural arithmetic and powers of two.

# Formalization notes

The precision budget is the protected-radius denominator plus two.
That denominator is quasipolynomial in the input order and accuracy, so
this conservative choice also gives a quasipolynomial iteration budget.
The resource estimate and concrete RAM execution are separate obligations.
-/

namespace Lax263307.AlgorithmParameters

def logarithm (n : ℕ) : ℕ := Nat.log2 (2 * n) + 1
def load (B n D : ℕ) : ℕ := 12 * B * D * logarithm n
def targetThreshold (a K B n D : ℕ) : ℕ := K * (load B n D + 1) ^ (4 * a + 2)
def sparsity (a K B n D : ℕ) : ℕ := 2 * targetThreshold a K B n D
def level (a K B n D : ℕ) : ℕ := sparsity a K B n D * (Nat.log2 n + 1)
def cutoff (a K B n D : ℕ) : ℕ := max (targetThreshold a K B n D) (level a K B n D)
def floorDenominator (a K B n D : ℕ) : ℕ :=
  2 * n * sparsity a K B n D * (Nat.log2 n + 1)
def momentFloor (a K B n D : ℕ) : ℚ :=
  1 / (floorDenominator a K B n D : ℚ) ^ level a K B n D
def radiusDenominator (a K B n D : ℕ) : ℕ :=
  256 * MomentLP.dimension n (level a K B n D) * n ^ 2 * D ^ 2 *
    floorDenominator a K B n D ^ level a K B n D
def precision (a K B n D : ℕ) : ℕ := radiusDenominator a K B n D + 2
def iterations (a K B n D : ℕ) : ℕ :=
  RoundedOracleSearch.steps (MomentLP.dimension n (level a K B n D)) (precision a K B n D)

axiom budgets {a K B n D k : ℕ} (hK : 0 < K) (hB : 0 < B)
    (hD : 4 ≤ D) (large : cutoff a K B n D < k) :
    0 < load B n D ∧ 0 < sparsity a K B n D ∧ 0 < level a K B n D ∧
      0 < (1 / (D : ℝ)) ∧ (1 / (D : ℝ)) ≤ 1 / 4 ∧
      12 * (B : ℝ) * ((Nat.log2 (2 * n) : ℝ) + 1) ≤
        (1 / (D : ℝ)) * load B n D ∧
      (sparsity a K B n D : ℝ) * ((Nat.log2 n : ℝ) + 1) ≤ level a K B n D ∧
      (K : ℝ) * ((load B n D : ℝ) + 1) ^ (4 * a + 2) ≤ k ∧
      (2 * K : ℝ) * ((load B n D : ℝ) + 1) ^ (4 * a + 2) ≤ sparsity a K B n D

axiom conditioning_floor (a K B n D : ℕ) :
    (momentFloor a K B n D : ℝ) =
      HeavyConditioning.probabilityFloor n (sparsity a K B n D) ^ level a K B n D

axiom protected_radius {a K B n D : ℕ} (hK : 0 < K) (hn : 0 < n) (hD : 0 < D) :
    2 ≤ precision a K B n D ∧
      ((2 : ℝ) ^ precision a K B n D)⁻¹ ≤
        (momentFloor a K B n D : ℝ) /
          (256 * (MomentLP.dimension n (level a K B n D) : ℝ) * (n : ℝ) ^ 2 * (D : ℝ) ^ 2)

end Lax263307.AlgorithmParameters
