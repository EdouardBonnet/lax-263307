import Lax263307.Entropy

/-!
---
title: Edge mass bounds the average entropy decrease
type: lemma
---
Let $\pi$ be a probability vector and let $q$ be a symmetric nonnegative
joint distribution with marginals $\pi$. Suppose $q_{uv}=0$ on edges of $G$.
For $\pi_v>0$, set $\pi^v_u=q_{uv}/\pi_v$. Then
$$H(\pi)-\sum_v\pi_v H(\pi^v)
  \ge\sum_{u,v:\,uv\in E(G)}\pi_u\pi_v.$$
Terms with $\pi_v=0$ have weight zero.

# Formalization notes

The lower bound uses $x\ln x\ge x-1$ on the support of $q$.
All edge pairs lie outside that support. Converting natural-log entropy
to bits only increases this nonnegative bound, since $0<\ln2\le1$.
-/

namespace Lax263307.EntropyGap

open Entropy

/-- The expected loss in entropy dominates the ordered adjacency mass. -/
axiom average_entropy_gap {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (π : Fin n → ℝ) (q : Fin n → Fin n → ℝ)
    (probability : IsProbability π) (nonnegative : ∀ u v, 0 ≤ q u v)
    (symmetric : ∀ u v, q u v = q v u)
    (marginals : ∀ v, (∑ u, q u v) = π v)
    (edge_zero : ∀ u v, G.Adj u v → q u v = 0) :
    adjacencyMass G π ≤ entropy π - ∑ v, π v * entropy (fun u => q u v / π v)

end Lax263307.EntropyGap
