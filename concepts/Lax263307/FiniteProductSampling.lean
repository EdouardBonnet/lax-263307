import Lax263307.PathSampling
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Logic.Equiv.Prod

/-!
---
title: Finite product sampling and coordinate marginals
type: lemma
---
Independent finite coordinates have total product mass one. Restricting to
any injectively selected coordinates recovers the product law on precisely
those coordinates. The remaining coordinates sum out to one.

# Attribution

Finite probability algebra for Bonnet–Chang's coupled sampling in Lemma 11.
-/

namespace Lax263307.FiniteProductSampling

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

noncomputable def weight (f : ι → κ → ℝ) (φ : ι → κ) : ℝ := ∏ a, f a (φ a)

axiom normalized (f : ι → κ → ℝ) (mass : ∀ a, (∑ x, f a x) = 1) :
    (∑ φ : ι → κ, weight f φ) = 1

axiom embedding_marginal {k : ℕ} (f : ι → κ → ℝ)
    (mass : ∀ a, (∑ x, f a x) = 1) (j : Fin k ↪ ι) (H : (Fin k → κ) → ℝ) :
    (∑ φ : ι → κ, weight f φ * H (fun a => φ (j a))) =
      ∑ ψ : Fin k → κ, weight (fun a => f (j a)) ψ * H ψ

end Lax263307.FiniteProductSampling
