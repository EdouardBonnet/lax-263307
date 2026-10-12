import Lax263307.EntropyDecrease
import Lax263307.EntropyBounds

/-!
---
title: A small conditioning set gives low edge cost
type: theorem
---
Let $p,k,r$ be positive integers with $r\ge2p\log_2 n$, and let
$y\in R_r(G,k)$. There exists a set $A$ of size at most $r$ with $y_A>0$
such that the conditioned costs lie in $[0,1]$, have total mass $k$, and satisfy
$$\sum_{uv\in E(G)}x_u x_v\le k^2/p.$$

# Attribution

Bonnet–Chang, the existence assertion in Lemma 12.

# Formalization notes

This statement supplies the mathematical guarantee for finite enumeration.
The rational implementation and its running-time bound are separate proof
obligations. No entropy values need to be computed by the enumeration.
-/

namespace Lax263307.ConditioningExistence

open LinearRelaxation ConditioningDistribution Entropy

/-- Existence of the conditioning set promised by Lemma 12. -/
axiom exists_low_edge_cost {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k r p : ℕ) (y : MomentVector n r) (feasible : IsFeasible G k r y)
    (target_positive : 0 < k) (level_positive : 0 < r) (threshold_positive : 0 < p)
    (budget : 2 * (p : ℝ) * Real.logb 2 n ≤ r) :
    ∃ A : Finset (Fin n), A.card ≤ r ∧ 0 < value y A ∧
      (∀ v, 0 ≤ conditioned y A v ∧ conditioned y A v ≤ 1) ∧
      (∑ v, conditioned y A v) = k ∧
      edgeCost G (conditioned y A) ≤ (k : ℝ) ^ 2 / p

end Lax263307.ConditioningExistence
