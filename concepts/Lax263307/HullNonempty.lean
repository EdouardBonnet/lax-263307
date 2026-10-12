import Lax263307.LinearRelaxation

/-!
---
title: The exact hull is nonempty precisely at feasible targets
type: theorem
---
The polytope $P_r(G,k)$ is nonempty if and only if $G$ has an independent
set of size $k$. Thus certifying emptiness rules out the target $k$.

# Attribution

Bonnet–Chang, Section 5.1, equation (20).
-/

namespace Lax263307.HullNonempty

open LinearRelaxation

/-- Nonemptiness of the exact hull is equivalent to existence of an independent set. -/
axiom hull_nonempty_iff {n : ℕ} (G : SimpleGraph (Fin n)) (k r : ℕ) :
    (independentSetHull G k r).Nonempty ↔
      ∃ I : Finset (Fin n), G.IsIndepSet (I : Set (Fin n)) ∧ I.card = k

end Lax263307.HullNonempty
