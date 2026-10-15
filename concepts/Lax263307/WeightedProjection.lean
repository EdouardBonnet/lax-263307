import Lax263307.RoundingBounds
import Lax263307.BlowUpIndependentSets

/-!
---
title: Projecting an unweighted approximation gives a weighted approximation
type: lemma
---
Let an $n$-vertex graph have nonnegative rational weights, with positive
maximum weight $W$, and let $0<\varepsilon<1$.
Use multiplicities $t_v=\lfloor w_v/\tau\rfloor$, where
$\tau=\varepsilon W/(2n)$. A $(1-\varepsilon/2)$-approximate independent
set in the blow-up projects to a $(1-\varepsilon)$-approximate weighted
independent set in the original graph.

# Attribution

Bonnet–Chang, the approximation guarantee in the proof of Theorem 2.

# Formalization notes

The main theorem combines this approximation transfer with separator
preservation under blow-ups and the running-time bound.
-/

namespace Lax263307.WeightedProjection

open WeightedIndependentSet WeightRounding IndependentBlowUp

/-- The two half-accuracy losses combine into the requested weighted guarantee. -/
axiom approximation_transfer {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ)
    (ε : ℚ) (nonnegative : ∀ v, 0 ≤ w v) (positive_order : 0 < n)
    (positive_accuracy : 0 < ε) (accuracy_lt_one : ε < 1)
    (positive_maximum : 0 < maximumWeight w)
    (K : Finset (Vertex (copies w ε)))
    (approximation : IsCardinalityApproximation G (copies w ε) (ε / 2) K) :
    IsApproximation G w ε (project K)

end Lax263307.WeightedProjection
