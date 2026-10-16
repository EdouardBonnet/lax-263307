import Lax263307.IndependentBlowUp

/-!
---
title: Independent sets lift and project through a blow-up
type: lemma
---
An independent set of the original graph lifts to an independent set
containing all its copies. An independent set of copies projects to an
independent set of the original graph. The lift of $I$ has size
$\sum_{v\in I}t_v$, and every set of copies $K$ satisfies
$|K|\le\sum_{v\in\operatorname{project}(K)}t_v$.
-/

namespace Lax263307.BlowUpIndependentSets

open IndependentBlowUp

/-- Taking all copies preserves independence. -/
axiom lift_independent {n : ℕ} (G : SimpleGraph (Fin n)) (copies : Fin n → ℕ)
    (I : Finset (Fin n)) (independent : G.IsIndepSet (I : Set (Fin n))) :
    (graph G copies).IsIndepSet (lift copies I : Set (Vertex copies))

/-- Projecting any independent set of copies preserves independence. -/
axiom project_independent {n : ℕ} (G : SimpleGraph (Fin n)) (copies : Fin n → ℕ)
    (K : Finset (Vertex copies)) (independent : (graph G copies).IsIndepSet (K : Set (Vertex copies))) :
    G.IsIndepSet (project K : Set (Fin n))

/-- The lift contains exactly the sum of the selected vertices' multiplicities. -/
axiom lift_cardinality {n : ℕ} (copies : Fin n → ℕ) (I : Finset (Fin n)) :
    (lift copies I).card = ∑ v ∈ I, copies v

/-- A set of copies is contained in the complete lift of its projection. -/
axiom projection_capacity {n : ℕ} (copies : Fin n → ℕ) (K : Finset (Vertex copies)) :
    K.card ≤ ∑ v ∈ project K, copies v

end Lax263307.BlowUpIndependentSets
