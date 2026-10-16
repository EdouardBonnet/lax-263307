import Lax263307.ConditionedCosts

/-!
---
title: Joint distributions for the entropy-decrease argument
type: lemma
---
For $y\in R_r(G,k)$, $k>0$, $|A|<r$, and $y_A>0$, set
$$\pi_v=\frac{y_{A\cup\{v\}}}{k y_A},\qquad
q_{uv}=\frac{y_{A\cup\{u,v\}}}{k^2 y_A}.$$
The vector $\pi$ is a probability distribution. The entries of $q$ are
nonnegative and symmetric, with both marginals equal to $\pi$, and $q_{uv}=0$
whenever $uv$ is an edge. For $\pi_v>0$, the distribution after conditioning
on $v$ is given by $\pi^v_u=q_{uv}/\pi_v$.
-/

namespace Lax263307.ConditioningDistribution

open LinearRelaxation

/-- Normalize conditioned vertex costs to a probability vector. -/
noncomputable def marginal {n r : ℕ} (y : MomentVector n r)
    (A : Finset (Fin n)) (k : ℕ) (v : Fin n) : ℝ :=
  conditioned y A v / k

/-- The joint distribution obtained from moments containing two extra vertices. -/
noncomputable def joint {n r : ℕ} (y : MomentVector n r)
    (A : Finset (Fin n)) (k : ℕ) (u v : Fin n) : ℝ :=
  value y (insert u (insert v A)) / ((k : ℝ) ^ 2 * value y A)

/-- The probability and conditional-probability identities for the moment relaxation. -/
axiom distribution_identities {n : ℕ} (G : SimpleGraph (Fin n)) (k r : ℕ)
    (y : MomentVector n r) (feasible : IsFeasible G k r y)
    (A : Finset (Fin n)) (size : A.card < r) (positive : 0 < value y A)
    (target_positive : 0 < k) :
    (∀ v, 0 ≤ marginal y A k v) ∧
    (∑ v : Fin n, marginal y A k v) = 1 ∧
    (∀ u v, 0 ≤ joint y A k u v) ∧
    (∀ u v, joint y A k u v = joint y A k v u) ∧
    (∀ v, (∑ u : Fin n, joint y A k u v) = marginal y A k v) ∧
    (∀ u v, G.Adj u v → joint y A k u v = 0) ∧
    (∀ u v, 0 < marginal y A k v →
      marginal y (insert v A) k u = joint y A k u v / marginal y A k v)

end Lax263307.ConditioningDistribution
