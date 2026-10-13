import Lax263307.ComponentCutEncoding

/-!
---
title: Quantitative gaps for recursive component cuts
type: theorem
---
The collected component normal has sum of absolute coefficients at most
|C|+u, hence at most 2n for u≤n. A heavy part of conditioned cost at least
delta*k/(2n), queried at floor((1-delta)*cost)+1, gives a feasible-point
cut gap at least eta*delta²*k/(2n) whenever the conditioning moment is
at least eta>0. Nearby queried centers retain a positive gap.

# Formalization notes

The coordinate error radius eta*delta²/(8n²) leaves a query gap of at
least eta*delta²/(4n). A central cut with gap Delta retains an entire
coordinate cube of radius Delta/(4n) around every valid hull point.
This is the buffer needed for ellipsoid stopping even when the exact
independent-set hull has no ambient interior.
-/

namespace Lax263307.StrongComponentGaps

open LinearRelaxation ComponentCutEncoding

axiom coefficient_l1 {n r : ℕ} (A C : Finset (Fin n)) (u : ℕ) :
    (∑ B : Coordinate n r, |(coefficient A C u B : ℝ)|) ≤ C.card + u

axiom evaluation_stable {n r : ℕ} (A C : Finset (Fin n)) (u : ℕ)
    (x y : MomentVector n r) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (near : ∀ B, |x B - y B| ≤ ρ) :
    |evaluate (coefficient A C u) x - evaluate (coefficient A C u) y| ≤ (C.card + u) * ρ

axiom component_gap {n r : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ)
    (y : MomentVector n r) (A C : Finset (Fin n)) (u : ℕ)
    (size : A.card ≤ r) (bound : IsIndependenceBound G C u)
    (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) (hn : 0 < n) (hk : 0 < k)
    (moment : η ≤ value y A)
    (heavy : δ * (k : ℝ) / (2 * n) ≤ ∑ v ∈ C, conditioned y A v)
    (rounded : (u : ℝ) ≤ (1 - δ) * ∑ v ∈ C, conditioned y A v) :
    (∀ z ∈ independentSetHull G k r, evaluate (coefficient A C u) z ≤ 0) ∧
      η * δ ^ 2 * (k : ℝ) / (2 * n) ≤ evaluate (coefficient A C u) y

axiom query_gap {n r : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ)
    (x y : MomentVector n r) (A C : Finset (Fin n)) (u : ℕ)
    (size : A.card ≤ r) (bound : IsIndependenceBound G C u) (upper : u ≤ n)
    (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) (hn : 0 < n) (hk : 0 < k)
    (moment : η ≤ value y A)
    (heavy : δ * (k : ℝ) / (2 * n) ≤ ∑ v ∈ C, conditioned y A v)
    (rounded : (u : ℝ) ≤ (1 - δ) * ∑ v ∈ C, conditioned y A v)
    (near : ∀ B, |x B - y B| ≤ η * δ ^ 2 / (8 * (n : ℝ) ^ 2)) :
    (∀ z ∈ independentSetHull G k r, evaluate (coefficient A C u) z ≤ 0) ∧
      η * δ ^ 2 / (4 * n) ≤ evaluate (coefficient A C u) x

axiom central_cut_buffer {n r : ℕ} (A C : Finset (Fin n)) (u : ℕ) (upper : u ≤ n)
    (x z : MomentVector n r) (Δ : ℝ) (positive : 0 < Δ) (hn : 0 < n)
    (valid : evaluate (coefficient A C u) z ≤ 0)
    (gap : Δ ≤ evaluate (coefficient A C u) x)
    (perturbed : MomentVector n r)
    (near : ∀ B, |perturbed B - z B| ≤ Δ / (4 * n)) :
    evaluate (coefficient A C u) perturbed ≤ evaluate (coefficient A C u) x - Δ / 2

end Lax263307.StrongComponentGaps
