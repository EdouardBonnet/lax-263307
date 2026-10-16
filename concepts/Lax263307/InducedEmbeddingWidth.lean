import Lax263307.HostRestriction
import Lax263307.IsolatedEmbeddingTransfer
import Lax263307.GraphClasses
import Lax263307.RoutePruning
import Lax263307.SampledAlmostEmbeddings

/-!
---
title: A class width bound obstructs induced route sampling
type: lemma
---
Suppose every graph in a hereditary class has a decomposition whose bag
size is bounded by a monotone function $W$ of its edge count. An induced
almost-embedding of a source graph of maximum degree $d$, with routes of
size at most $L$, transfers this to source bags of size at most
$\max\{1,2dW(d|E(H)|L^2)\}$.

Discarding long routes adds at most their number to this bound on treewidth
plus one. A good sample with total size at most $4M$ therefore gives a
number $q$ of discarded edges with $Lq\le4M$ and the resulting source
width bound. This is the quantitative obstruction used with a source
family of linear treewidth.

# Formalization notes

The monotone class bag bound is an explicit hypothesis here. The main theorem derives it
from its separator hypothesis.
-/

namespace Lax263307.InducedEmbeddingWidth

open PathSampling (adjacencyProbability collisionProbability expectedSize)
open RouteDistributions (Distribution)
open RoutePruning (longEdges)
open AlmostEmbeddings InducedRouteEdges Lax228581.Treewidth
open GraphClasses

def HasBagBound (C : GraphClass) (W : ℕ → ℕ) : Prop :=
  ∀ n (G : SimpleGraph (Fin n)), G ∈ C n →
    ∃ D : TreeDecomposition G, ∀ i, (D.bag i).card ≤ W G.edgeSet.ncard

axiom transfer_class_bound {t n : ℕ} (C : GraphClass) (hereditary : IsHereditary C)
    (W : ℕ → ℕ) (monotone : Monotone W) (class_bound : HasBagBound C W)
    (H : SimpleGraph (Fin t)) [DecidableRel H.Adj] (G : SimpleGraph (Fin n))
    (member : G ∈ C n) (E : AlmostEmbedding H G) (induced : IsInduced E) (d L : ℕ)
    (degree_bound : ∀ v, H.degree v ≤ d) (length_bound : ∀ e, (E.route e).card ≤ L) :
    ∃ D : TreeDecomposition H, ∀ i, (D.bag i).card ≤
      max 1 (2 * d * W (d * H.edgeSet.ncard * L ^ 2))

axiom treewidth_after_pruning {t n : ℕ} (C : GraphClass) (hereditary : IsHereditary C)
    (W : ℕ → ℕ) (monotone : Monotone W) (class_bound : HasBagBound C W)
    (H : SimpleGraph (Fin t)) [DecidableRel H.Adj] (G : SimpleGraph (Fin n))
    (member : G ∈ C n) (E : AlmostEmbedding H G) (induced : IsInduced E) (d L : ℕ)
    (degree_bound : ∀ v, H.degree v ≤ d) :
    treewidth H + 1 ≤ max 1 (2 * d * W (d * H.edgeSet.ncard * L ^ 2)) +
      (longEdges E L).card

axiom sampled_width_bound {t n q : ℕ} (C : GraphClass) (hereditary : IsHereditary C)
    (W : ℕ → ℕ) (monotone : Monotone W) (class_bound : HasBagBound C W)
    (H : SimpleGraph (Fin t)) [DecidableRel H.Adj] (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (member : G ∈ C n) (D : Distribution G q) (hn : 0 < n)
    (d L : ℕ) (degree_bound : ∀ v, H.degree v ≤ d) (M : ℝ) (positive : 0 < M)
    (bad_budget : (H.edgeSet.ncard : ℝ) ^ 2 * (collisionProbability D.toSampling +
      adjacencyProbability G D.toSampling) ≤ 1 / 4)
    (length_budget : (H.edgeSet.ncard : ℝ) * expectedSize D.toSampling ≤ M) :
    ∃ removed : ℕ, (L : ℝ) * removed ≤ 4 * M ∧
      treewidth H + 1 ≤ max 1 (2 * d * W (d * H.edgeSet.ncard * L ^ 2)) + removed

end Lax263307.InducedEmbeddingWidth
