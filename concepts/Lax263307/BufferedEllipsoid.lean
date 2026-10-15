import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
---
title: Protected balls for the rounded ellipsoid method
type: lemma
---
Scaling a moment vector in the unit cube by 4N puts it well inside the
initial unit ball. A perturbation of Euclidean radius at most one quarter
stays in that ball. Euclidean balls are contained in the corresponding
coordinate cubes, so the central-cut buffers apply to them. Every nonzero
integer normal has squared Euclidean norm at least one.

# Formalization notes

The squared norms use finite dot products, matching the registered LP
ellipsoid sequence. These geometric estimates do not assume that the
independent-set hull has interior. Coordinate scaling is defined over an
arbitrary field so its rational specialization is computable.
-/

namespace Lax263307.BufferedEllipsoid

open Matrix

def scale {K : Type} [Field K] {n : ℕ} (z : Fin n → K) : Fin n → K := fun i => z i / (4 * (n : K))

axiom coordinate_ball_bound {n : ℕ} (e : Fin n → ℝ) (ρ : ℝ) (nonnegative : 0 ≤ ρ)
    (ball : e ⬝ᵥ e ≤ ρ ^ 2) : ∀ i, |e i| ≤ ρ

axiom scaled_cube_norm {n : ℕ} (positive : 0 < n) (z : Fin n → ℝ)
    (cube : ∀ i, 0 ≤ z i ∧ z i ≤ 1) : scale z ⬝ᵥ scale z ≤ (1 / 16 : ℝ)

axiom initial_ball {n : ℕ} (positive : 0 < n) (z : Fin n → ℝ)
    (cube : ∀ i, 0 ≤ z i ∧ z i ≤ 1) (ρ : ℝ) (nonnegative : 0 ≤ ρ) (small : ρ ≤ 1 / 4)
    (e : Fin n → ℝ) (ball : e ⬝ᵥ e ≤ ρ ^ 2) :
    (scale z + e) ⬝ᵥ (scale z + e) ≤ 1

axiom integer_normal_norm {n : ℕ} (a : Fin n → ℤ) (nonzero : ∃ i, a i ≠ 0) :
    1 ≤ (fun i => (a i : ℝ)) ⬝ᵥ (fun i => (a i : ℝ))

end Lax263307.BufferedEllipsoid
