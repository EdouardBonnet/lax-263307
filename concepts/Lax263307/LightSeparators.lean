import Lax263307.EdgeBagBounds
import Lax263307.ForcedSeparation
import Lax263307.CutTraces

/-!
---
title: Balanced light separators from the registered flow-cut solver
type: theorem
---
A hereditary class with strongly edge-sublinear separators has fixed positive
integer constants a,K,B. A cost vector with coordinates in [0,1], total
mass at most k, and edge cost at most k²/p admits a balanced separator of
cost at most delta*k when k and p exceed the stated polynomial thresholds.
The cut trace uses at most n calls and keeps its actual covering shores.

# Formalization notes

The load parameter ell needs only a multiple of log n / delta. This theorem
instantiates the remainder oracle using the registered directed split solver:
restriction cannot increase costs, the larger remainder supplies the load
scale inequality, and a sufficiently large finite rational capacity excludes
expensive split arcs. Orienting the cut toward its smaller shore supplies
the exclusive-piece bound. The accumulated trace cost is at most delta*k.
Actual RAM construction and iteration costs remain separate obligations.

# Attribution

Bonnet–Chang, Lemmas 7–8 and 11.
-/

namespace Lax263307.LightSeparators

open scoped NNRat
open GraphClasses EdgeSublinearSeparators Entropy RepeatedCutAccounting

axiom class_light_separator (C : GraphClass) (hereditary : IsHereditary C)
    (separators : HasStronglyEdgeSublinearSeparators C) :
    ∃ a K B : ℕ, 0 < a ∧ 0 < K ∧ 0 < B ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G ∈ C n → 0 < n → ∀ (x : Fin n → ℚ≥0) (k p δ : ℝ) (ℓ : ℕ),
      0 < k → 0 < p → 0 < δ → 0 < ℓ →
      (∀ v, (x v : ℝ) ≤ 1) → (∑ v, (x v : ℝ)) ≤ k →
      edgeCost G (fun v => (x v : ℝ)) ≤ k ^ 2 / p →
      12 * (B : ℝ) * ((Nat.log2 (2 * n) : ℝ) + 1) ≤ δ * ℓ →
      (K : ℝ) * ((ℓ : ℝ) + 1) ^ (4 * a + 2) ≤ k →
      (2 * K : ℝ) * ((ℓ : ℝ) + 1) ^ (4 * a + 2) ≤ p →
      ∃ q, ∃ T : Lax263307.CutTraces.Trace G Finset.univ q,
        q ≤ n ∧ IsBalancedSeparator G (Lax263307.CutTraces.separator T) ∧
          cost (fun v => (x v : ℝ)) (Lax263307.CutTraces.separator T) ≤ δ * k

end Lax263307.LightSeparators
