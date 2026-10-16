import Lax263307.Entropy
import Mathlib.Data.Finset.Card

/-!
---
title: Collision and length bounds for independently sampled paths
type: lemma
---
Let $Q$ be a random vertex set and let $q_v=\Pr[v\in Q]$. Two independent
samples intersect with probability at most $\sum_v q_v^2$. The probability
that an edge joins their vertex sets is at most the ordered adjacency mass
$\sum_{uv\in E(G)}2q_uq_v$. Also $\mathbb E[|Q|]=\sum_vq_v$.

Consequently, if $q_v\le\ell x_v/k$, $0\le x_v\le1$, $\sum_vx_v\le k$ with $k>0$,
and $e_G(x)\le k^2/p$ with $p>0$, these bounds are respectively
$\ell^2/k$, $2\ell^2/p$, and $\ell$.

# Formalization notes

A finite distribution is given explicitly by its outcome probabilities.
The pair probabilities are products, expressing independent sampling.
The estimates depend only on the vertex sets of the sampled paths, so the
definitions allow arbitrary finite vertex sets.
-/

namespace Lax263307.PathSampling

open Entropy (adjacencyMass edgeCost)
/-- Finite outcome probabilities and their associated vertex sets. -/
structure Distribution (n q : ℕ) where
  /-- Probability of each outcome. -/
  probability : Fin q → ℝ
  /-- Probabilities are nonnegative. -/
  nonnegative : ∀ i, 0 ≤ probability i
  /-- Total probability is one. -/
  normalized : (∑ i, probability i) = 1
  /-- The vertices used by each outcome. -/
  vertices : Fin q → Finset (Fin n)

/-- Probability of using a particular vertex. -/
noncomputable def load {n q : ℕ} (P : Distribution n q) (v : Fin n) : ℝ :=
  ∑ i, if v ∈ P.vertices i then P.probability i else 0

/-- Expected number of used vertices. -/
noncomputable def expectedSize {n q : ℕ} (P : Distribution n q) : ℝ :=
  ∑ i, P.probability i * ((P.vertices i).card : ℝ)

/-- Probability that independent outcomes have a common vertex. -/
noncomputable def collisionProbability {n q : ℕ} (P : Distribution n q) : ℝ :=
  ∑ i, ∑ j, if ¬Disjoint (P.vertices i) (P.vertices j) then
    P.probability i * P.probability j else 0

/-- Probability that a graph edge joins independent outcomes. -/
noncomputable def adjacencyProbability {n q : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (P : Distribution n q) : ℝ :=
  ∑ i, ∑ j, if ∃ u ∈ P.vertices i, ∃ v ∈ P.vertices j, G.Adj u v then
    P.probability i * P.probability j else 0

/-- Sum of vertex-use probabilities equals expected size. -/
axiom expected_size_identity {n q : ℕ} (P : Distribution n q) :
  expectedSize P = ∑ v, load P v

/-- The union bound for intersection of two independent samples. -/
axiom collision_union_bound {n q : ℕ} (P : Distribution n q) :
  collisionProbability P ≤ ∑ v, (load P v) ^ 2

/-- The union bound for edges joining two independent samples. -/
axiom adjacency_union_bound {n q : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (P : Distribution n q) :
  adjacencyProbability G P ≤ adjacencyMass G (load P)

/-- The load hypotheses imply the three estimates used in sampling. -/
axiom sampling_bounds {n q : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (P : Distribution n q) (x : Fin n → ℝ) (k ℓ p : ℝ)
    (k_positive : 0 < k) (ℓ_nonnegative : 0 ≤ ℓ) (p_positive : 0 < p)
    (cost_bounds : ∀ v, 0 ≤ x v ∧ x v ≤ 1) (mass : (∑ v, x v) ≤ k)
    (load_bound : ∀ v, load P v ≤ ℓ * x v / k)
    (edge_bound : edgeCost G x ≤ k ^ 2 / p) :
    collisionProbability P ≤ ℓ ^ 2 / k ∧
      adjacencyProbability G P ≤ 2 * ℓ ^ 2 / p ∧ expectedSize P ≤ ℓ

end Lax263307.PathSampling
