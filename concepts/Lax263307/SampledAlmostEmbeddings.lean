import Lax263307.CoupledSamplingBounds
import Lax263307.AlmostEmbeddings

/-!
---
title: An induced almost-embedding from a good route sample
type: theorem
---
Sample the edges of any finite simple source graph from a uniform-endpoint
route distribution. If the interaction union bound is at most $1/4$ and
the expected total route size is at most $M>0$, some sample gives an induced
almost-embedding of total route size at most $4M$.

# Formalization notes

Enumerate unordered source edges only for the finite sampling construction.
Their two endpoints are distinct, and nonincident edges have four distinct
endpoints. A sampled route's ordered vertex list is a graph walk, so its
vertex set induces a connected graph. The shared vertex-image assignment
provides the endpoint condition in the almost-embedding.

# Attribution

Bonnet–Chang, the initial induced almost-embedding in Lemma 11.
-/

namespace Lax263307.SampledAlmostEmbeddings

open Lax263307.RouteDistributions Lax263307.AlmostEmbeddings

axiom exists_induced_almost_embedding {t n q : ℕ} (H : SimpleGraph (Fin t)) [DecidableRel H.Adj]
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Distribution G q) (hn : 0 < n)
    (M : ℝ) (positive : 0 < M)
    (bad_budget : (H.edgeSet.ncard : ℝ) ^ 2 * (Lax263307.PathSampling.collisionProbability D.toSampling +
      Lax263307.PathSampling.adjacencyProbability G D.toSampling) ≤ 1 / 4)
    (length_budget : (H.edgeSet.ncard : ℝ) * Lax263307.PathSampling.expectedSize D.toSampling ≤ M) :
    ∃ E : AlmostEmbedding H G, IsInduced E ∧ (∑ e, ((E.route e).card : ℝ)) ≤ 4 * M

end Lax263307.SampledAlmostEmbeddings
