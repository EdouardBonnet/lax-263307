import Lax263307.CostSamplingObstruction
import Lax263307.PowerBagBounds
import Lax263307.SourceGraphs
import Lax263307.WidthGrowth

/-!
---
title: Sparse bounded-load route distributions are impossible
type: theorem
---
Suppose a hereditary class has a uniform power bound on decomposition bags.
There is a fixed positive integer $K$ such that a class member cannot support
a uniform-endpoint route distribution with vertex loads at most
$\ell x_v/k$, costs in $[0,1]$ of total mass at most $k$, and edge cost at
most $k^2/p$, when $k\ge K(\ell+1)^{4a+2}$ and
$p\ge2K(\ell+1)^{4a+2}$.

The registered source family supplies a graph large enough to contradict
the sampled width upper bound, while its size overshoot keeps its edge count
within the probability budgets.

# Formalization notes

The power bag bound is an explicit hypothesis. Deriving it from strongly
edge-sublinear separators is a remaining part of the main proof. No source
graph construction is needed by the separator algorithm: this family is
used only in the contradiction that rules out its high-flow branch.

# Attribution

Bonnet–Chang, the sampled-path contradiction of Lemma 11, with the registered
subcubic source family from Lax920634.
-/

namespace Lax263307.NoBoundedLoadRoutes

open Lax263307.GraphClasses Lax263307.PowerBagBounds Lax228581.Treewidth

axiom no_bounded_load_routes (C : GraphClass) (hereditary : IsHereditary C)
    (a A : ℕ) (a_positive : 0 < a) (A_positive : 0 < A) (class_bound : HasPowerBagBound C a A) :
    ∃ K : ℕ, 0 < K ∧ ∀ (n q : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G ∈ C n → ∀ (D : Lax263307.RouteDistributions.Distribution G q), 0 < n →
      ∀ (ℓ : ℕ), 0 < ℓ → ∀ (x : Fin n → ℝ) (k p : ℝ), 0 < k → 0 < p →
      (∀ v, 0 ≤ x v ∧ x v ≤ 1) → (∑ v, x v) ≤ k →
      (∀ v, Lax263307.PathSampling.load D.toSampling v ≤ (ℓ : ℝ) * x v / k) →
      Lax263307.Entropy.edgeCost G x ≤ k ^ 2 / p →
      (K : ℝ) * ((ℓ : ℝ) + 1) ^ (4 * a + 2) ≤ k →
      (2 * K : ℝ) * ((ℓ : ℝ) + 1) ^ (4 * a + 2) ≤ p → False

end Lax263307.NoBoundedLoadRoutes
