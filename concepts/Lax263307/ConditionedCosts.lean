import Lax263307.LinearRelaxation

/-!
---
title: Conditioning preserves bounded costs and total mass
type: lemma
---
Let $y\in R_r(G,k)$ and let $|A|\le r$ with $y_A>0$.
The conditioned costs $x_v=y_{A\cup\{v\}}/y_A$ lie in $[0,1]$,
sum to $k$, and equal one for every $v\in A$.
Whenever $x_v>0$, the enlarged conditioning set still has positive moment.
-/

namespace Lax263307.ConditionedCosts

open LinearRelaxation

/-- Basic invariants of the conditioning operation. -/
axiom conditioning_invariants {n : ℕ} (G : SimpleGraph (Fin n)) (k r : ℕ)
    (y : MomentVector n r) (feasible : IsFeasible G k r y)
    (A : Finset (Fin n)) (size : A.card ≤ r) (positive : 0 < value y A) :
    (∀ v, 0 ≤ conditioned y A v ∧ conditioned y A v ≤ 1) ∧
    (∑ v : Fin n, conditioned y A v) = k ∧
    (∀ v ∈ A, conditioned y A v = 1) ∧
    (∀ v, 0 < conditioned y A v → 0 < value y (insert v A))

end Lax263307.ConditionedCosts
