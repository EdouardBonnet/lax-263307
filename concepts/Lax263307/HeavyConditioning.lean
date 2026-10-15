import Lax263307.ConditioningDistribution
import Lax263307.EntropyGap
import Lax263307.EntropyBounds
import Mathlib.Data.Nat.Log

/-!
---
title: Conditioning with a quantitative moment lower bound
type: lemma
---
A high edge cost forces entropy decrease even after conditioning choices
with extremely small marginal probability are excluded. Some choice of
probability at least tau=1/(2np(log2 n+1)) decreases entropy by more than
1/p. Within r≥p(log2 n+1) steps, a sparse conditioning set is therefore
reached with raw moment at least tau^r.

# Formalization notes

This strengthens the positive-moment existence guarantee. The quantitative
lower bound prevents a violated component inequality from having an
arbitrarily small raw gap at a feasible query. It is used by the strong-gap
ellipsoid argument; the rational search is formalized in `HeavyRationalConditioning`.
-/

namespace Lax263307.HeavyConditioning

open LinearRelaxation ConditioningDistribution Entropy

noncomputable def probabilityFloor (n p : ℕ) : ℝ :=
  1 / (2 * (n : ℝ) * p * ((Nat.log2 n : ℝ) + 1))

axiom heavy_entropy_decrease {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k r p : ℕ) (y : MomentVector n r) (feasible : IsFeasible G k r y)
    (A : Finset (Fin n)) (size : A.card < r) (positive : 0 < value y A)
    (target_positive : 0 < k) (threshold_positive : 0 < p) (order_positive : 0 < n)
    (expensive : (k : ℝ) ^ 2 / p < edgeCost G (conditioned y A)) :
    ∃ v : Fin n, probabilityFloor n p ≤ marginal y A k v ∧
      entropy (marginal y (insert v A) k) < entropy (marginal y A k) - 1 / p

axiom heavy_low_edge_cost {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k r p : ℕ) (y : MomentVector n r) (feasible : IsFeasible G k r y)
    (order_positive : 0 < n) (target_positive : 0 < k)
    (level_positive : 0 < r) (threshold_positive : 0 < p)
    (budget : (p : ℝ) * ((Nat.log2 n : ℝ) + 1) ≤ r) :
    ∃ A : Finset (Fin n), A.card ≤ r ∧ probabilityFloor n p ^ r ≤ value y A ∧
      0 < value y A ∧ (∀ v, 0 ≤ conditioned y A v ∧ conditioned y A v ≤ 1) ∧
      (∑ v, conditioned y A v) = k ∧ edgeCost G (conditioned y A) ≤ (k : ℝ) ^ 2 / p

end Lax263307.HeavyConditioning
