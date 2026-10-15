import Lax263307.LinearRelaxation

/-!
---
title: Valid separating inequalities from independent-set bounds
type: lemma
---
Suppose every independent set in $G[C]$ has size at most $u$.
For $|A|\le r$, every $z\in P_r(G,k)$ satisfies
$$\sum_{v\in C}z_{A\cup\{v\}}\le u z_A.$$

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

end Lax263307.ComponentCuts
