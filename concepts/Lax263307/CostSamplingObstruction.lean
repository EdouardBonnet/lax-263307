import Lax263307.InducedEmbeddingWidth

/-!
---
title: A width obstruction from sparse costs and bounded route loads
type: lemma
---
Assume vertex costs lie in $[0,1]$, have total mass at most $k>0$, and
edge cost at most $k^2/p$. A route distribution with vertex loads at most
$\ell x_v/k$ satisfies the sampling budgets for any source graph with
$m$ edges when $k\ge8m^2\ell^2$ and $p\ge16m^2\ell^2$.
Consequently, for a source graph of maximum degree $d$, a monotone class
bag bound $W$ forces a discarded-edge count $q$ with
$Lq\le4m\ell$ and the pruned source treewidth-plus-one bound.

# Formalization notes

The class bag bound is an explicit intermediate hypothesis. This lemma
combines the probability estimates with the sampled width obstruction.
The main theorem obtains the bag bound from its separator hypothesis.
-/

namespace Lax263307.CostSamplingObstruction

open Entropy (edgeCost)
open PathSampling (load)
open RouteDistributions (Distribution)
open GraphClasses InducedEmbeddingWidth Lax228581.Treewidth

axiom cost_width_obstruction {t n q : ℕ} (C : GraphClass) (hereditary : IsHereditary C)
    (W : ℕ → ℕ) (monotone : Monotone W) (class_bound : HasBagBound C W)
    (H : SimpleGraph (Fin t)) [DecidableRel H.Adj] (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (member : G ∈ C n) (D : Distribution G q) (hn : 0 < n)
    (d L : ℕ) (degree_bound : ∀ v, H.degree v ≤ d) (edge_positive : 0 < H.edgeSet.ncard)
    (x : Fin n → ℝ) (k ℓ p : ℝ) (k_positive : 0 < k) (ℓ_positive : 0 < ℓ) (p_positive : 0 < p)
    (cost_bounds : ∀ v, 0 ≤ x v ∧ x v ≤ 1) (mass : (∑ v, x v) ≤ k)
    (load_bound : ∀ v, load D.toSampling v ≤ ℓ * x v / k)
    (edge_bound : edgeCost G x ≤ k ^ 2 / p)
    (target_large : 8 * (H.edgeSet.ncard : ℝ) ^ 2 * ℓ ^ 2 ≤ k)
    (sparsity_large : 16 * (H.edgeSet.ncard : ℝ) ^ 2 * ℓ ^ 2 ≤ p) :
    ∃ removed : ℕ, (L : ℝ) * removed ≤ 4 * (H.edgeSet.ncard : ℝ) * ℓ ∧
      treewidth H + 1 ≤ max 1 (2 * d * W (d * H.edgeSet.ncard * L ^ 2)) + removed

end Lax263307.CostSamplingObstruction
