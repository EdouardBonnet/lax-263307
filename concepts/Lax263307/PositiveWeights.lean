import Lax263307.WeightedIndependentSet

/-!
---
title: Removing nonpositive weights
type: lemma
---
Replace each rational weight $w_v$ by $\max(w_v,0)$. An approximation for
these nonnegative weights yields the same approximation for the original
weights by removing the nonpositive-weight vertices of its returned set.
If all weights are nonpositive, the empty set is optimal.

# Formalization notes

Clipping changes only vertex weights, so the graph stays in its original
class. Removing selected vertices preserves independence. The approximation
transfer assumes an accuracy in $[0,1]$.
-/

namespace Lax263307.PositiveWeights

open WeightedIndependentSet

/-- Clip negative weights to zero. -/
def positiveWeights {n : ℕ} (w : Fin n → ℚ) : Fin n → ℚ := fun v => max (w v) 0

/-- Retain only the strictly positive-weight vertices of a returned set. -/
def discardNonpositive {n : ℕ} (w : Fin n → ℚ) (I : Finset (Fin n)) : Finset (Fin n) :=
  I.filter fun v => 0 < w v

/-- Approximation for clipped weights transfers to arbitrary signed weights. -/
axiom signed_weight_transfer {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ)
    (ε : ℚ) (accuracy_nonnegative : 0 ≤ ε) (accuracy_le_one : ε ≤ 1)
    (I : Finset (Fin n)) (approximation : IsApproximation G (positiveWeights w) ε I) :
    IsApproximation G w ε (discardNonpositive w I)

/-- The empty set solves instances whose weights are all nonpositive. -/
axiom nonpositive_case {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ)
    (nonpositive : ∀ v, w v ≤ 0) (ε : ℚ) (accuracy_nonnegative : 0 ≤ ε)
    (accuracy_le_one : ε ≤ 1) : IsApproximation G w ε ∅

end Lax263307.PositiveWeights
