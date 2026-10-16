import Lax263307.ComponentCuts
import Mathlib.Data.Fintype.Powerset

/-!
---
title: Integer coefficients of recursive separating cuts
type: lemma
---
The cut for a part $C$ and bound $u$ is
$$\sum_{v\in C}z_{A\cup\{v\}}-u z_A\le0.$$
Collect repeated coordinates into an integer coefficient vector. Evaluating
that vector gives exactly the left-hand side of the component inequality.
-/

namespace Lax263307.ComponentCutEncoding

open LinearRelaxation

/-- The coefficient at one coordinate, after collecting all repeated terms. -/
def coefficient {n r : ℕ} (A C : Finset (Fin n)) (u : ℕ)
    (B : Coordinate n r) : ℤ :=
  (∑ v ∈ C, if insert v A = B.val then 1 else 0) -
    if A = B.val then (u : ℤ) else 0

/-- Evaluate the coefficient vector in the real coordinate space. -/
noncomputable def evaluate {n r : ℕ} (a : Coordinate n r → ℤ)
    (z : MomentVector n r) : ℝ := ∑ B, (a B : ℝ) * z B

/-- The collected coefficient vector represents exactly the intended cut. -/
axiom evaluation_identity {n r : ℕ} (A C : Finset (Fin n)) (u : ℕ)
    (size : A.card ≤ r) (z : MomentVector n r) :
    evaluate (coefficient A C u) z =
      (∑ v ∈ C, value z (insert v A)) - (u : ℝ) * value z A

end Lax263307.ComponentCutEncoding
