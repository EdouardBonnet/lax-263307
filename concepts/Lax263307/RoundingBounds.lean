import Lax263307.WeightRounding

/-!
---
title: Rounding loses at most one weight unit per vertex
type: lemma
---
For nonnegative weights and $\tau>0$, the multiplicities
$t_v=\lfloor w_v/\tau\rfloor$ satisfy
$$w_v-\tau\le\tau t_v\le w_v.$$
Consequently, for each vertex set $J$,
$$\tau\sum_{v\in J}t_v\ge w(J)-|J|\tau.$$
With $\tau=\varepsilon W/(2n)$, the total number of copies is at most
$2n^2/\varepsilon$.
-/

namespace Lax263307.RoundingBounds

open WeightedIndependentSet WeightRounding

/-- The floor approximation loses at most one positive scaling unit. -/
axiom pointwise_bounds {n : ℕ} (w : Fin n → ℚ) (τ : ℚ)
    (nonnegative : ∀ v, 0 ≤ w v) (positive_scale : 0 < τ) :
    ∀ v, τ * (roundedCopies w τ v : ℚ) ≤ w v ∧
      w v - τ ≤ τ * (roundedCopies w τ v : ℚ)

/-- The additive rounding loss is at most the set cardinality times the scaling unit. -/
axiom set_rounding_loss {n : ℕ} (w : Fin n → ℚ) (τ : ℚ)
    (nonnegative : ∀ v, 0 ≤ w v) (positive_scale : 0 < τ) (J : Finset (Fin n)) :
    weight w J - (J.card : ℚ) * τ ≤ τ * ((∑ v ∈ J, roundedCopies w τ v : ℕ) : ℚ)

/-- The rounded blow-up order is polynomial in the order and inverse accuracy. -/
axiom total_copy_bound {n : ℕ} (w : Fin n → ℚ) (ε : ℚ)
    (nonnegative : ∀ v, 0 ≤ w v) (positive_order : 0 < n)
    (positive_accuracy : 0 < ε) (positive_maximum : 0 < maximumWeight w) :
    ((∑ v, copies w ε v : ℕ) : ℚ) ≤ 2 * (n : ℚ) ^ 2 / ε

end Lax263307.RoundingBounds
