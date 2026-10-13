import Lax263307.CoupledRouteSampling
import Lax263307.SamplingOutcomes

/-!
---
title: A good coupled sample with bounded total route size
type: theorem
---
For a source graph with $m$ edges, the expected total sampled route size is
$m$ times the single-route expectation. The probability that some pair of
nonincident routes intersects or has a host edge between them is at most
$m^2$ times the sum of the single-pair collision and adjacency probabilities.
If that bound is at most $1/4$ and the expected total size is at most $M>0$,
there is a positive-probability sample with no such interaction and total
route size at most $4M$.

# Attribution

Bonnet–Chang, the union bound and Markov step in Lemma 11.
-/

namespace Lax263307.CoupledSamplingBounds

open Lax263307.RouteDistributions Lax263307.CoupledRouteSampling

noncomputable def Interaction {n q : ℕ} (G : SimpleGraph (Fin n))
    (D : Distribution G q) (i j : Fin q) : Prop :=
  ¬Disjoint (D.route i).toFinset (D.route j).toFinset ∨
    ∃ u ∈ (D.route i).toFinset, ∃ v ∈ (D.route j).toFinset, G.Adj u v

noncomputable instance {n q : ℕ} (G : SimpleGraph (Fin n))
    (D : Distribution G q) (i j : Fin q) : Decidable (Interaction G D i j) := Classical.propDecidable _

noncomputable def badProbability {n q t m : ℕ} (G : SimpleGraph (Fin n))
    (D : Distribution G q) (a b : Fin m → Fin t) : ℝ := by
  classical
  exact ∑ φ, ∑ ψ, if ∃ e f, Function.Injective ![a e, b e, a f, b f] ∧ Interaction G D (ψ e) (ψ f)
    then jointWeight D a b φ ψ else 0

axiom total_length_expectation {n q t m : ℕ} {G : SimpleGraph (Fin n)}
    (D : Distribution G q) (hn : 0 < n) (a b : Fin m → Fin t)
    (nonloop : ∀ e, a e ≠ b e) :
    (∑ φ, ∑ ψ, jointWeight D a b φ ψ * (∑ e, ((D.route (ψ e)).toFinset.card : ℝ))) =
      (m : ℝ) * Lax263307.PathSampling.expectedSize D.toSampling

axiom bad_probability_bound {n q t m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : Distribution G q) (hn : 0 < n) (a b : Fin m → Fin t) :
    badProbability G D a b ≤ (m : ℝ) ^ 2 *
      (Lax263307.PathSampling.collisionProbability D.toSampling +
        Lax263307.PathSampling.adjacencyProbability G D.toSampling)

axiom good_route_sample {n q t m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : Distribution G q) (hn : 0 < n) (a b : Fin m → Fin t) (nonloop : ∀ e, a e ≠ b e)
    (M : ℝ) (positive : 0 < M)
    (bad_budget : (m : ℝ) ^ 2 * (Lax263307.PathSampling.collisionProbability D.toSampling +
      Lax263307.PathSampling.adjacencyProbability G D.toSampling) ≤ 1 / 4)
    (length_budget : (m : ℝ) * Lax263307.PathSampling.expectedSize D.toSampling ≤ M) :
    ∃ φ : Fin t → Fin n, ∃ ψ : Fin m → Fin q,
      0 < jointWeight D a b φ ψ ∧
      (∀ e f, Function.Injective ![a e, b e, a f, b f] → ¬Interaction G D (ψ e) (ψ f)) ∧
      (∑ e, ((D.route (ψ e)).toFinset.card : ℝ)) ≤ 4 * M

end Lax263307.CoupledSamplingBounds
