import Lax263307.ConditioningDistribution
import Lax263307.EntropyGap

/-!
---
title: High edge cost forces a strict entropy decrease
type: theorem
---
Let $y\in R_r(G,k)$, $k>0$, $|A|<r$, and $y_A>0$.
For a positive integer $p$, if the conditioned costs satisfy
$$\sum_{uv\in E(G)}x_u x_v>k^2/p,$$
then some vertex $v$ has $\pi_v>0$ and conditioning on $v$ decreases entropy
by more than $2/p$:
$$H(\pi^v)<H(\pi)-2/p.$$

# Attribution

Bonnet–Chang, proof of Lemma 12, the consequence of equation (18).
-/

namespace Lax263307.EntropyDecrease

open LinearRelaxation ConditioningDistribution Entropy

/-- An expensive edge product forces a positive-cost conditioning step. -/
axiom exists_entropy_decrease {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k r p : ℕ) (y : MomentVector n r) (feasible : IsFeasible G k r y)
    (A : Finset (Fin n)) (size : A.card < r) (positive : 0 < value y A)
    (target_positive : 0 < k) (threshold_positive : 0 < p)
    (expensive : (k : ℝ) ^ 2 / p < edgeCost G (conditioned y A)) :
    ∃ v : Fin n, 0 < marginal y A k v ∧
      entropy (marginal y (insert v A) k) < entropy (marginal y A k) - 2 / p

end Lax263307.EntropyDecrease
