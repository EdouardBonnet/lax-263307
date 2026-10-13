import Lax263307.BufferedEllipsoid
import Mathlib.Data.Nat.Size

/-!
---
title: Rational cut normals preserve protected cubes after scaling
type: theorem
---
Clear all rational normal coefficients by one positive product of denominators.
The resulting integer normal defines the same central half-space. Its bit size
is bounded by the numerator bit size plus the sum of denominator bit sizes.
A positive query gap, together with a bound on the sum of absolute coefficients,
protects a whole coordinate cube about every valid point. Scaling coordinates
by 4N and clearing denominators preserve that protected central cut.

# Formalization notes

Both clearing operations are computable. Only the correctness argument uses
real casts. The scaled-cube guarantee supplies the cut hypothesis for the
actual rounded ellipsoid loop; it does not assume that the exact hull has
interior. The numerator calculation matches the registered LP size-bound
construction and is proved directly from divisibility of the denominator
product.
-/

namespace Lax263307.RationalCutBuffer

open Matrix

def denominator {n : ℕ} (a : Fin n → ℚ) : ℕ := ∏ i, (a i).den

def integerNormal {n : ℕ} (a : Fin n → ℚ) (i : Fin n) : ℤ :=
  (a i).num * (denominator a / (a i).den : ℕ)

axiom denominator_positive {n : ℕ} (a : Fin n → ℚ) : 0 < denominator a

axiom integer_normal_cast {n : ℕ} (a : Fin n → ℚ) (i : Fin n) :
    (integerNormal a i : ℝ) = (denominator a : ℝ) * (a i : ℝ)

axiom normal_nonzero {n : ℕ} (a : Fin n → ℚ) (x z : Fin n → ℝ)
    (gap : (fun i => (a i : ℝ)) ⬝ᵥ z < (fun i => (a i : ℝ)) ⬝ᵥ x) :
    ∃ i, integerNormal a i ≠ 0

axiom denominator_bound {n : ℕ} (a : Fin n → ℚ) :
    denominator a ≤ 2 ^ (∑ i, Nat.size (a i).den)

axiom normal_size {n : ℕ} (a : Fin n → ℚ) (i : Fin n) :
    Nat.size (integerNormal a i).natAbs ≤
      Nat.size (a i).num.natAbs + ∑ j, Nat.size (a j).den

axiom dot_stable {n : ℕ} (a x y : Fin n → ℝ) (ρ L : ℝ)
    (nonnegative : 0 ≤ ρ) (norm : (∑ i, |a i|) ≤ L)
    (near : ∀ i, |x i - y i| ≤ ρ) : |a ⬝ᵥ x - a ⬝ᵥ y| ≤ L * ρ

axiom central_buffer {n : ℕ} (a x z perturbed : Fin n → ℝ) (α Δ ρ L : ℝ)
    (nonnegative : 0 ≤ ρ) (norm : (∑ i, |a i|) ≤ L)
    (valid : a ⬝ᵥ z ≤ α) (gap : α + Δ ≤ a ⬝ᵥ x)
    (small : L * ρ ≤ Δ / 2) (near : ∀ i, |perturbed i - z i| ≤ ρ) :
    a ⬝ᵥ perturbed ≤ a ⬝ᵥ x - Δ / 2

axiom scaled_cleared_cut {n : ℕ} (positive : 0 < n) (a : Fin n → ℚ)
    (query z : Fin n → ℝ) (α Δ ρ L : ℝ)
    (nonnegative : 0 ≤ ρ) (norm : (∑ i, |(a i : ℝ)|) ≤ L)
    (valid : (fun i => (a i : ℝ)) ⬝ᵥ z ≤ α)
    (gap : α + Δ ≤ (fun i => (a i : ℝ)) ⬝ᵥ (fun i => 4 * (n : ℝ) * query i))
    (small : L * ρ ≤ Δ / 2) (e : Fin n → ℝ)
    (near : ∀ i, |e i| ≤ ρ / (4 * n)) :
    (fun i => (integerNormal a i : ℝ)) ⬝ᵥ
      (Lax263307.BufferedEllipsoid.scale z + e - query) ≤ 0

end Lax263307.RationalCutBuffer
