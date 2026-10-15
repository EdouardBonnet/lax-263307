import Lax263307.AlmostEmbeddings
import Lax263307.EdgeDeletionWidth

/-!
---
title: Discarding long almost-embedding routes
type: lemma
---
Discard each source edge whose host route uses more than $L$ vertices. The
number of discarded edges times $L$ is at most the original total route
size. The remaining graph retains an induced almost-embedding with every
route using at most $L$ vertices. Edge deletion may create isolated source
vertices; the transfer with singleton bags handles them separately.

# Attribution

Bonnet–Chang, the long-route deletion step in Lemma 11.
-/

namespace Lax263307.RoutePruning

open AlmostEmbeddings

noncomputable def longEdges {t n : ℕ} {H : SimpleGraph (Fin t)} [DecidableRel H.Adj]
    {G : SimpleGraph (Fin n)} (E : AlmostEmbedding H G) (L : ℕ) : Finset (Sym2 (Fin t)) := by
  classical
  exact (Finset.univ.filter fun e : H.edgeSet => L < (E.route e).card).image Subtype.val

axiom long_edge_count {t n : ℕ} (H : SimpleGraph (Fin t)) [DecidableRel H.Adj]
    (G : SimpleGraph (Fin n)) (E : AlmostEmbedding H G) (L : ℕ) :
    L * (longEdges E L).card ≤ ∑ e : H.edgeSet, (E.route e).card

axiom prune_routes {t n : ℕ} (H : SimpleGraph (Fin t)) [DecidableRel H.Adj]
    (G : SimpleGraph (Fin n)) (E : AlmostEmbedding H G) (induced : IsInduced E) (L : ℕ) :
    ∃ E' : AlmostEmbedding (H.deleteEdges (↑(longEdges E L) : Set (Sym2 (Fin t)))) G,
      IsInduced E' ∧ (∀ e, (E'.route e).card ≤ L)

end Lax263307.RoutePruning
