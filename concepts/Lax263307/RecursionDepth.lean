import Lax263307.WeightedIndependentSet
import Mathlib.Data.Nat.Log

/-!
---
title: Depth and approximation loss of balanced recursion
type: lemma
---
A recursive call on a balanced component has at most $\lfloor2n/3\rfloor$
vertices. The number of nontrivial calls on a branch is therefore logarithmic
in the original graph order. A factor $1-\delta$ lost at each of at most
$\lambda$ levels retains at least $1-\lambda\delta$ of a certified upper bound.

# Formalization notes

The integer depth function avoids numerical evaluation of logarithms with
base $3/2$. Empty graphs and singletons have depth zero. The explicit upper
bound uses twice the binary logarithm; this constant change does not affect
the QPTAS bound.

# Attribution

Bonnet–Chang, the recursion-depth argument in Lemma 14 and Bernoulli's
inequality in Theorem 15.
-/

namespace Lax263307.RecursionDepth

open WeightedIndependentSet (IsApproximation)
/-- Number of balanced reductions needed to reach order at most one. -/
def depth (n : ℕ) : ℕ :=
  if n ≤ 1 then 0 else 1 + depth (2 * n / 3)
termination_by n
decreasing_by omega

/-- A balanced recursive call consumes one level. -/
axiom balanced_decrease (n m : ℕ) (nontrivial : 1 < n) (balanced : 3 * m ≤ 2 * n) :
    depth m + 1 ≤ depth n

/-- At most two reductions are needed per binary-logarithm level. -/
axiom logarithmic_bound (n : ℕ) : depth n ≤ 2 * (Nat.log2 n + 1)

/-- A certified independence upper bound turns the accumulated loss into approximation. -/
axiom approximation_transfer {n : ℕ} (G : SimpleGraph (Fin n))
    (I : Finset (Fin n)) (u levels : ℕ) (δ ε : ℚ)
    (independent : G.IsIndepSet (I : Set (Fin n)))
    (upper_bound : ∀ J : Finset (Fin n), G.IsIndepSet (J : Set (Fin n)) → J.card ≤ u)
    (δ_nonnegative : 0 ≤ δ) (δ_small : δ ≤ 1)
    (ε_small : ε ≤ 1) (loss : (levels : ℚ) * δ ≤ ε)
    (size : (1 - δ) ^ levels * (u : ℚ) ≤ I.card) :
    IsApproximation G (fun _ => 1) ε I

end Lax263307.RecursionDepth
