import Lax263307.RoutingNormalization
import Lax263307.SplitPathProjection

/-!
---
title: Graph-route distributions from high-value split flows
type: theorem
---
A feasible directed split flow of value at least $1/\gamma$ yields a finite
distribution of simple original graph routes with uniform ordered endpoints.
The probability that a route uses vertex $v$ is at most
$\gamma x_v/n^2$. Both endpoints count toward this load; equal original
endpoints are allowed and their route is a singleton.

# Formalization notes

Routes carrying positive probability are simple graph paths. Zero-probability
outcomes may have empty routes. Arc-to-path conversion is used only for the
existence argument, so this statement imposes no algorithm for constructing
the distribution. The underlying solver still returns an arc-flow certificate.

# Attribution

Bonnet–Chang, flow normalization and endpoint-inclusive loads in Lemma 7.
-/

namespace Lax263307.RouteDistributions

open scoped NNReal NNRat
open Lax263307.RoutingNormalization Lax263307.VertexSplitting
open Lax455465.ConcurrentFlow

structure Distribution {n : ℕ} (G : SimpleGraph (Fin n)) (q : ℕ) where
  probability : Fin q → ℝ
  nonnegative : ∀ i, 0 ≤ probability i
  normalized : (∑ i, probability i) = 1
  route : Fin q → List (Fin n)
  valid : ∀ i, 0 < probability i → (route i).Nodup ∧ (route i).IsChain G.Adj ∧ route i ≠ []
  uniform : ∀ u v, (∑ i, if (route i).head? = some u ∧ (route i).getLast? = some v then
    probability i else 0) = 1 / (n : ℝ) ^ 2

noncomputable def Distribution.toSampling {n q : ℕ} {G : SimpleGraph (Fin n)}
    (D : Distribution G q) : Lax263307.PathSampling.Distribution n q where
  probability := D.probability
  nonnegative := D.nonnegative
  normalized := D.normalized
  vertices i := (D.route i).toFinset

/-- Normalize finite graph routes commodity by commodity. -/
axiom finite_routes {n q : ℕ} (G : SimpleGraph (Fin n)) (hn : 0 < n)
    (w : Fin q → ℝ) (E : Fin n → Fin n → Fin q → Prop)
    (w_nonnegative : ∀ i, 0 ≤ w i) (γ : ℝ) (γ_positive : 0 < γ)
    (lower : ∀ u v, 1 / γ ≤ routed w E u v)
    (Q : Fin q → List (Fin n))
    (routes : ∀ u v i, E u v i → (Q i).Nodup ∧ (Q i).IsChain G.Adj ∧
      (Q i).head? = some u ∧ (Q i).getLast? = some v) :
    ∃ D : Distribution G (n * (n * q)), ∀ z,
      Lax263307.PathSampling.load D.toSampling z ≤ γ / (n : ℝ) ^ 2 *
        (∑ i, w i * (if z ∈ Q i then (1 : ℝ) else 0))

/-- A high-value split arc-flow certificate yields a bounded-load route distribution. -/
axiom split_arc_distribution {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hn : 0 < n) (x : Fin n → ℚ≥0) (large : ℚ≥0) (γ : ℝ) (γ_positive : 0 < γ)
    (f : ℝ≥0) (high : 1 / γ ≤ (f : ℝ)) (F : ArcFlow (2 * n))
    (feasible : IsArcConcurrentFlow .directed (splitInstance G x large).network
      (splitInstance G x large).weights f F) :
    ∃ q, ∃ D : Distribution G q, ∀ z,
      Lax263307.PathSampling.load D.toSampling z ≤ γ * (x z : ℝ) / (n : ℝ) ^ 2

end Lax263307.RouteDistributions
