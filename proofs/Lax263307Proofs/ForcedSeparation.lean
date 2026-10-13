import Lax263307.ForcedSeparation
import Mathlib.Tactic

namespace Lax263307Proofs.ForcedSeparation

open scoped NNReal NNRat
open Lax263307.GraphClasses Lax263307.PowerBagBounds Lax263307.VertexSplitting
open Lax455465.ProductNetwork Lax455465.ConcurrentFlow

/--
---
conclusion: Lax263307.ForcedSeparation.certificate_separation
---
Apply the proved split certificate dichotomy. A high-value flow would
produce a uniform-endpoint route distribution. Its load bound and the
scale inequality give loads at most ell*x/k, contradicting the proved
sparse-route obstruction. The remaining branch gives exactly the projected
cut shores and separator cost bound.
-/
theorem certificate_separation (C : GraphClass) (hereditary : IsHereditary C)
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
        4 * ρ * (leftShore certificate.cut).card * (rightShore certificate.cut).card / γ := by
  classical
  obtain ⟨K, hK, impossible⟩ := Lax263307.NoBoundedLoadRoutes.no_bounded_load_routes
    C hereditary a A a_positive A_positive class_bound
  refine ⟨K, hK, ?_⟩
  intro n G _ hG hn x large certificate ρ γ k p ℓ hℓ hρ hγ hk hp hscale hcost hmass hedge
    htarget hsparse hadmissible hflow hratio hlarge
  rcases Lax263307.VertexSplitting.flow_or_separation G x large certificate ρ γ hρ hγ
    hadmissible hflow hratio hlarge with ⟨hhigh, hvalid⟩ | hseparation
  · obtain ⟨q, D, hD⟩ := Lax263307.RouteDistributions.split_arc_distribution G hn x large γ hγ
      (certificate.flow.value : ℝ≥0) hhigh certificate.flow.flow hvalid
    have hden : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    have hfactor : γ / (n : ℝ) ^ 2 ≤ (ℓ : ℝ) / k := (div_le_div_iff₀ hden hk).mpr hscale
    have hload (v : Fin n) : Lax263307.PathSampling.load D.toSampling v ≤ (ℓ : ℝ) * (x v : ℝ) / k := by
      calc
        _ ≤ γ * (x v : ℝ) / (n : ℝ) ^ 2 := hD v
        _ = γ / (n : ℝ) ^ 2 * (x v : ℝ) := by ring
        _ ≤ (ℓ : ℝ) / k * (x v : ℝ) := mul_le_mul_of_nonneg_right hfactor (by positivity)
        _ = _ := by ring
    exact (impossible n q G hG D hn ℓ hℓ (fun v => (x v : ℝ)) k p hk hp
      (fun v => ⟨by positivity, hcost v⟩) hmass hload hedge htarget hsparse).elim
  · exact hseparation


end Lax263307Proofs.ForcedSeparation
