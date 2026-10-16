import Lax263307.LinearRelaxation

/-!
---
title: Independent-set encodings satisfy the relaxation
type: lemma
---
Every independent set $I$ of size $k$ gives a feasible point of $R_r(G,k)$
by setting $y_A=\mathbf1[A\subseteq I]$. Consequently
$P_r(G,k)\subseteq R_r(G,k)$.
-/

namespace Lax263307.RelaxationFeasibility

open LinearRelaxation

/-- All indicator encodings satisfy the five families of constraints. -/
axiom indicator_feasible {n : ℕ} (G : SimpleGraph (Fin n)) (k r : ℕ)
    (I : Finset (Fin n)) (independent : G.IsIndepSet (I : Set (Fin n)))
    (cardinality : I.card = k) : IsFeasible G k r (indicator r I)

/-- The exact independent-set hull is contained in the relaxation. -/
axiom hull_feasible {n : ℕ} (G : SimpleGraph (Fin n)) (k r : ℕ)
    (y : MomentVector n r) (member : y ∈ independentSetHull G k r) :
    IsFeasible G k r y

end Lax263307.RelaxationFeasibility
