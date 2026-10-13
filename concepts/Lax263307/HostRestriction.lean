import Lax263307.InducedRouteEdges

/-!
---
title: Restricting an induced almost-embedding to its route union
type: theorem
---
Relabel the host graph induced by the nonempty union of edge routes onto
Fin. The resulting graph embeds inducedly in the original host, has the
same induced edge count, and supports the same induced almost-embedding
with each route size preserved. Isolated source vertices may receive an
arbitrary host image because they impose no endpoint condition.

# Attribution

The host restriction before applying the class width bound in Bonnet–Chang,
proof of Lemma 11.
-/

namespace Lax263307.HostRestriction

open Lax263307.AlmostEmbeddings Lax263307.InducedRouteEdges

axiom restrict_to_route_union {t n : ℕ} (H : SimpleGraph (Fin t)) [DecidableRel H.Adj]
    (G : SimpleGraph (Fin n)) (E : AlmostEmbedding H G) (induced : IsInduced E)
    (nonempty : (routeUnion E).Nonempty) :
    ∃ r, ∃ K : SimpleGraph (Fin r), ∃ _f : K ↪g G, ∃ E' : AlmostEmbedding H K,
      IsInduced E' ∧ (∀ e, (E'.route e).card = (E.route e).card) ∧
      K.edgeSet.ncard = (G.induce (↑(routeUnion E) : Set (Fin n))).edgeSet.ncard

end Lax263307.HostRestriction
