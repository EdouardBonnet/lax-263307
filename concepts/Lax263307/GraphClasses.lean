import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
---
title: Hereditary graph classes
type: definition
---
A class of finite simple graphs is hereditary if it is closed under taking
induced subgraphs and under isomorphism.

# Formalization notes

Graphs are represented on vertex sets $\{0,\ldots,n-1\}$. Closure under
induced embeddings includes both induced subgraphs and all relabelings.
No algorithm for recognizing membership in the class is assumed.
-/

namespace Lax263307.GraphClasses

/-- A class of finite simple graphs, represented on numbered vertex sets. -/
abbrev GraphClass := (n : ℕ) → Set (SimpleGraph (Fin n))

/-- Every graph that embeds as an induced subgraph of a member also belongs. -/
def IsHereditary (C : GraphClass) : Prop :=
  ∀ (m n : ℕ) (H : SimpleGraph (Fin m)) (G : SimpleGraph (Fin n)),
    G ∈ C n → Nonempty (H ↪g G) → H ∈ C m

end Lax263307.GraphClasses
