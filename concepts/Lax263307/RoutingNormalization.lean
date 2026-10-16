import Lax263307.PathSampling

/-!
---
title: Uniform endpoint normalization of finite path flows
type: lemma
---
Normalize each of the $n^2$ ordered endpoint commodities to mass $1/n^2$.
If every commodity has routed mass at least $1/\gamma$, normalization
increases any nonnegative load by at most $\gamma/n^2$. Each flow record
belongs to at most one endpoint pair, so records are counted only once.
The statement includes diagonal commodities and applies to vertex loads
that count both route endpoints.
-/

namespace Lax263307.RoutingNormalization

open scoped Classical

def IsUniquePair {n q : ℕ} (E : Fin n → Fin n → Fin q → Prop) : Prop :=
  ∀ i u v u' v', E u v i → E u' v' i → u = u' ∧ v = v'

noncomputable def routed {n q : ℕ} (w : Fin q → ℝ)
    (E : Fin n → Fin n → Fin q → Prop) (u v : Fin n) : ℝ :=
  ∑ i, if E u v i then w i else 0

noncomputable def probability {n q : ℕ} (w : Fin q → ℝ)
    (E : Fin n → Fin n → Fin q → Prop) (u v : Fin n) (i : Fin q) : ℝ :=
  if E u v i then w i / (routed w E u v * (n : ℝ) ^ 2) else 0

/-- Nonnegative normalized probabilities with uniform ordered endpoints. -/
axiom normalization_correct {n q : ℕ} (w : Fin q → ℝ)
    (E : Fin n → Fin n → Fin q → Prop) (hn : 0 < n)
    (nonnegative : ∀ i, 0 ≤ w i) (positive : ∀ u v, 0 < routed w E u v) :
    (∀ u v i, 0 ≤ probability w E u v i) ∧
      (∀ u v, (∑ i, probability w E u v i) = 1 / (n : ℝ) ^ 2) ∧
      (∑ u, ∑ v, ∑ i, probability w E u v i) = 1

/-- Uniform commodity normalization preserves the scaled load bound. -/
axiom normalized_load_bound {n q : ℕ} (w : Fin q → ℝ)
    (E : Fin n → Fin n → Fin q → Prop) (hn : 0 < n)
    (nonnegative : ∀ i, 0 ≤ w i) (unique : IsUniquePair E)
    (γ : ℝ) (γ_positive : 0 < γ) (lower_bound : ∀ u v, 1 / γ ≤ routed w E u v)
    (cost : Fin q → ℝ) (cost_nonnegative : ∀ i, 0 ≤ cost i) :
    (∑ u, ∑ v, ∑ i, probability w E u v i * cost i) ≤
      γ / (n : ℝ) ^ 2 * (∑ i, w i * cost i)

end Lax263307.RoutingNormalization
