import Lax263307.BlowUpDecompositions
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
---
title: Deleting high-degree vertices in an independent blow-up
type: lemma
---
Let $H$ be an independent blow-up of a graph of treewidth at most $w$.
Delete the vertices $X$ whose degree exceeds an integer threshold $s$.
Then $s|X|\le 2|E(H)|$, and $H$ has a tree decomposition with bags of size
at most
$$|X|+\max\{1,s(w+1)\}.$$

Large fibres become isolated after this deletion. The remaining nonisolated
vertices therefore embed into a blow-up with at most $s$ copies per vertex.
The maximum with one covers singleton bags for isolated vertices, including
the edgeless case and threshold zero.
-/

namespace Lax263307.BlowUpDeletion

open IndependentBlowUp Lax228581.Treewidth

/-- The vertices removed at degree threshold `s`. -/
noncomputable def highDegree {n : ℕ} (G : SimpleGraph (Fin n))
    (copies : Fin n → ℕ) (s : ℕ) : Finset (Vertex copies) := by
  classical
  exact Finset.univ.filter fun v => s < (graph G copies).degree v

/-- The degree sum bounds the number of removed vertices. -/
axiom high_degree_card {n : ℕ} (G : SimpleGraph (Fin n))
    (copies : Fin n → ℕ) (s : ℕ) :
    s * (highDegree G copies s).card ≤ 2 * (graph G copies).edgeSet.ncard

/-- Lift bounded fibres, add singleton bags, and restore the deleted set. -/
axiom deletion_decomposition {n : ℕ} (G : SimpleGraph (Fin n))
    (copies : Fin n → ℕ) (s w : ℕ) (width : HasTreewidthAtMost G w) :
    ∃ D : TreeDecomposition (graph G copies),
      ∀ i, (D.bag i).card ≤ (highDegree G copies s).card + max 1 (s * (w + 1))

/-- Choosing the degree threshold balances the two terms of the estimate. -/
axiom power_bound {n : ℕ} (G : SimpleGraph (Fin n))
    (copies : Fin n → ℕ) (w : ℕ) (b c : ℝ) (hb : 0 ≤ b) (hb₁ : b < 1)
    (hc : 0 < c) (width : HasTreewidthAtMost G w)
    (width_bound : (w + 1 : ℕ) ≤
      c * Real.rpow ((graph G copies).edgeSet.ncard + 1) b) :
    ∃ D : TreeDecomposition (graph G copies), ∀ i,
      ((D.bag i).card : ℝ) ≤ (3 + 2 * c) *
        Real.rpow ((graph G copies).edgeSet.ncard + 1) ((1 + b) / 2)

end Lax263307.BlowUpDeletion
