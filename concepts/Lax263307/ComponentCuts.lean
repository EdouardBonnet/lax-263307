import Lax263307.LinearRelaxation

/-!
---
title: Valid separating inequalities from independent-set bounds
type: theorem
---
Suppose every independent set in $G[C]$ has size at most $u$.
For $|A|\le r$, every $z\in P_r(G,k)$ satisfies
$$\sum_{v\in C}z_{A\cup\{v\}}\le u z_A.$$
A query $y$ with $y_A>0$ violates this inequality precisely when its
conditioned costs satisfy $\sum_{v\in C}x_v>u$.

# Attribution

Bonnet–Chang, Lemma 13. The set $C$ need not be a connected component;
the algorithm applies this statement to the components left by a separator.
-/

namespace Lax263307.ComponentCuts

open LinearRelaxation

/-- A certified independence bound supplies an inequality valid on the exact hull. -/
axiom valid_cut {n : ℕ} (G : SimpleGraph (Fin n)) (k r : ℕ)
    (C : Finset (Fin n)) (u : ℕ) (bound : IsIndependenceBound G C u)
    (A : Finset (Fin n)) (size : A.card ≤ r)
    (z : MomentVector n r) (member : z ∈ independentSetHull G k r) :
    ∑ v ∈ C, value z (insert v A) ≤ (u : ℝ) * value z A

/-- The exact rational test used to detect a violated cut. -/
axiom violation_iff {n r : ℕ} (y : MomentVector n r)
    (A C : Finset (Fin n)) (u : ℕ) (positive : 0 < value y A) :
    (u : ℝ) < ∑ v ∈ C, conditioned y A v ↔
      (u : ℝ) * value y A < ∑ v ∈ C, value y (insert v A)

end Lax263307.ComponentCuts
