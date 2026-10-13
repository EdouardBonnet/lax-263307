import Lax263307.NoBoundedLoadRoutes
import Lax263307.RouteDistributions
import Lax263307.VertexSplitting

/-!
---
title: The split flow-cut certificate must give a cheap separation
type: theorem
---
In a hereditary class with a power bag bound, sufficiently large target and
sparsity parameters rule out the high-flow branch of the directed split
certificate. If $\gamma k\le\ell n^2$, its projected route loads would
meet the forbidden bounded-load distribution hypotheses. The returned cut
therefore projects to two nonempty covering shores with no cross edge and
separator cost at most $4\rho|A||B|/\gamma$.

# Formalization notes

The shores are the actual minus/plus port projections of the certificate's
cut. This is the certificate analysis needed by the repeated-cut procedure;
the registered RAM solver and the wrapper cost are handled separately.
The power bag premise is still to be derived from the main separator premise.

# Attribution

Bonnet–Chang, Lemma 7 with its high-flow branch excluded by Lemma 11.
-/

namespace Lax263307.ForcedSeparation

open scoped NNReal NNRat
open Lax263307.GraphClasses Lax263307.PowerBagBounds Lax263307.VertexSplitting
open Lax455465.ProductNetwork Lax455465.ConcurrentFlow

axiom certificate_separation (C : GraphClass) (hereditary : IsHereditary C)
    (a A : ℕ) (a_positive : 0 < a) (A_positive : 0 < A) (class_bound : HasPowerBagBound C a A) :
    ∃ K : ℕ, 0 < K ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G ∈ C n → 0 < n → ∀ (x : Fin n → ℚ≥0) (large : ℚ≥0)
      (certificate : Lax455465.FlowCutCertificate.Certificate (2 * n)) (ρ γ k p : ℝ) (ℓ : ℕ),
      0 < ℓ → 0 ≤ ρ → 0 < γ → 0 < k → 0 < p →
      γ * k ≤ (ℓ : ℝ) * (n : ℝ) ^ 2 → (∀ v, (x v : ℝ) ≤ 1) →
      (∑ v, (x v : ℝ)) ≤ k →
      Lax263307.Entropy.edgeCost G (fun v => (x v : ℝ)) ≤ k ^ 2 / p →
      (K : ℝ) * ((ℓ : ℝ) + 1) ^ (4 * a + 2) ≤ k →
      (2 * K : ℝ) * ((ℓ : ℝ) + 1) ^ (4 * a + 2) ≤ p →
      AdmissibleCut (splitInstance G x large).weights certificate.cut →
      IsArcConcurrentFlow .directed (splitInstance G x large).network
        (splitInstance G x large).weights (certificate.flow.value : ℝ≥0) certificate.flow.flow →
      (ratioCost (splitInstance G x large).network (splitInstance G x large).weights certificate.cut : ℝ) ≤
        ρ * (certificate.flow.value : ℝ) →
      ρ * (2 * n : ℕ) ^ 2 / γ < (large : ℝ) →
      (leftShore certificate.cut).Nonempty ∧ (rightShore certificate.cut).Nonempty ∧
      leftShore certificate.cut ∪ rightShore certificate.cut = Finset.univ ∧
      (∀ u ∈ leftShore certificate.cut \ rightShore certificate.cut,
        ∀ v ∈ rightShore certificate.cut \ leftShore certificate.cut, ¬G.Adj u v) ∧
      (∑ v ∈ leftShore certificate.cut ∩ rightShore certificate.cut, (x v : ℝ)) ≤
        4 * ρ * (leftShore certificate.cut).card * (rightShore certificate.cut).card / γ

end Lax263307.ForcedSeparation
