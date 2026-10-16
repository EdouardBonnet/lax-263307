import Lax263307.RouteDistributions

/-!
---
title: Conditioning graph routes on uniform endpoints
type: lemma
---
Multiply the probability of a route with endpoints $(u,v)$ by $n^2$ to
obtain the conditional route law for this ordered endpoint pair. Every
conditional law is a probability distribution supported on routes with
those endpoints. Averaging over a uniformly sampled pair recovers the
original law. Averaging independently over four endpoints gives the product
law for two routes. These identities support sampling nonincident source
edges while sharing endpoint images for incident edges.
-/

namespace Lax263307.ConditionalRoutes

open RouteDistributions

noncomputable def conditional {n q : ℕ} {G : SimpleGraph (Fin n)}
    (D : Distribution G q) (u v : Fin n) (i : Fin q) : ℝ :=
  if (D.route i).head? = some u ∧ (D.route i).getLast? = some v then
    (n : ℝ) ^ 2 * D.probability i else 0

axiom conditional_correct {n q : ℕ} {G : SimpleGraph (Fin n)}
    (D : Distribution G q) (hn : 0 < n) (u v : Fin n) :
    (∀ i, 0 ≤ conditional D u v i) ∧ (∑ i, conditional D u v i) = 1 ∧
      (∀ i, 0 < conditional D u v i → (D.route i).head? = some u ∧
        (D.route i).getLast? = some v ∧ (D.route i).Nodup ∧ (D.route i).IsChain G.Adj)

axiom mixture_identity {n q : ℕ} {G : SimpleGraph (Fin n)}
    (D : Distribution G q) (i : Fin q) :
    (∑ u, ∑ v, conditional D u v i) = (n : ℝ) ^ 2 * D.probability i

axiom independent_pair_mixture {n q : ℕ} {G : SimpleGraph (Fin n)}
    (D : Distribution G q) (hn : 0 < n) (i j : Fin q) :
    (∑ u, ∑ v, ∑ s, ∑ t,
      conditional D u v i * conditional D s t j / (n : ℝ) ^ 4) =
        D.probability i * D.probability j

end Lax263307.ConditionalRoutes
