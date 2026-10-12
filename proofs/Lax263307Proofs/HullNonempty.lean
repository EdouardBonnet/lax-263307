import Lax263307.HullNonempty

namespace Lax263307Proofs.HullNonempty

open Lax263307.LinearRelaxation

/--
---
conclusion: Lax263307.HullNonempty.hull_nonempty_iff
---
The exact hull is nonempty if and only if there is an independent set
of the target cardinality.

# Proof strategy

A convex hull is nonempty precisely when its generating set is nonempty.
Unfolding the generating set gives the claimed independent set.

# Attribution

Bonnet–Chang, Section 5.1, equation (20).
-/
theorem hull_nonempty_iff {n : ℕ} (G : SimpleGraph (Fin n)) (k r : ℕ) :
    (independentSetHull G k r).Nonempty ↔
      ∃ I : Finset (Fin n), G.IsIndepSet (I : Set (Fin n)) ∧ I.card = k := by
  rw [independentSetHull, convexHull_nonempty_iff]
  constructor
  · rintro ⟨y, I, hI, hk, _⟩
    exact ⟨I, hI, hk⟩
  · rintro ⟨I, hI, hk⟩
    exact ⟨indicator r I, I, hI, hk, rfl⟩

end Lax263307Proofs.HullNonempty
