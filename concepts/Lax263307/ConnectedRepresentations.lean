import Lax263307.ConnectedBags

/-!
---
title: Tree-decomposition transfer through connected vertex representations
type: theorem
---
Represent each vertex of $H$ by a nonempty connected vertex set of $G$, with
intersecting sets for every edge of $H$. Suppose at most $B$ represented
vertices use any one vertex of $G$. A tree decomposition of $G$ with bags
of size at most $w$ then gives a tree decomposition of $H$ with bags of
size at most $Bw$.

# Attribution

The connected-set transfer used in Bonnet–Chang, Lemma 9.
-/

namespace Lax263307.ConnectedRepresentations

open Lax228581.Treewidth

/-- A connected vertex set in `G` for each vertex of `H`. -/
structure Representation {t n : ℕ} (H : SimpleGraph (Fin t))
    (G : SimpleGraph (Fin n)) where
  /-- The vertices used by a represented vertex. -/
  carrier : Fin t → Finset (Fin n)
  /-- Each carrier is nonempty and connected. -/
  connected : ∀ v, (G.induce (↑(carrier v) : Set (Fin n))).Connected
  /-- Carriers of adjacent vertices intersect. -/
  touching : ∀ u v, H.Adj u v → ∃ a, a ∈ carrier u ∧ a ∈ carrier v

/-- Which represented vertices use a particular host vertex. -/
def users {t n : ℕ} {H : SimpleGraph (Fin t)} {G : SimpleGraph (Fin n)}
    (R : Representation H G) (a : Fin n) : Finset (Fin t) :=
  Finset.univ.filter fun v => a ∈ R.carrier v

/-- Transfer a decomposition with a uniform bound on the representation load. -/
axiom transfer_decomposition {t n : ℕ} (H : SimpleGraph (Fin t))
    (G : SimpleGraph (Fin n)) (R : Representation H G)
    (B w : ℕ) (load_bound : ∀ a, (users R a).card ≤ B)
    (D : TreeDecomposition G) (bag_bound : ∀ i, (D.bag i).card ≤ w) :
    ∃ D' : TreeDecomposition H, ∀ i, (D'.bag i).card ≤ B * w

end Lax263307.ConnectedRepresentations
