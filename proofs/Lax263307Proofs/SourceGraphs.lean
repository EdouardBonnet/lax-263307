import Lax263307.SourceGraphs
import Mathlib.Tactic

namespace Lax263307Proofs.SourceGraphs

open Lax920634.ZigZagConstruction Lax920634.GraphEncoding Lax920634.SeedSearch
open Lax920634.EdgeExpansion Lax228581.Treewidth

theorem positive_factor (a b c : ℕ) (positive : 0 < c) (bound : c ≤ a * b) : 0 < a := by
  apply Nat.pos_of_ne_zero
  intro h
  rw [h, zero_mul] at bound
  omega

theorem positive_width (d : ℕ) : 0 < 24 * d + 1 := Nat.zero_lt_succ _

/--
---
conclusion: Lax263307.SourceGraphs.controlled_family
---
Use the registered graph at its specified size selector. Its registered
size, degree, and treewidth claims give all three bounds for the same graph.
The size constant is positive because the size-one request is met. Prove
positivity through generic arithmetic lemmas, leaving the fixed enormous
seed degree symbolic rather than evaluating its numeral.
-/
theorem controlled_family : ∃ widthConstant sizeConstant : ℕ,
    0 < widthConstant ∧ 0 < sizeConstant ∧
    ∀ request : ℕ, ∃ n, ∃ H : SimpleGraph (Fin n), request ≤ n ∧
      n ≤ sizeConstant * (request + 1) ∧ IsSubcubic H ∧
      n ≤ widthConstant * (treewidth H + 1) := by
  refine ⟨24 * degree + 1, 2 * degree * seedDegree ^ 4, positive_width degree, ?_, ?_⟩
  · have h := Lax920634.ConstructionSize.size_bounds 1
    have hpositive : 0 < order (selectedLevel 1) := lt_of_lt_of_le (Nat.zero_lt_succ 0) h.1
    exact positive_factor (2 * degree * seedDegree ^ 4) (1 + 1) (order (selectedLevel 1)) hpositive h.2
  · intro request
    refine ⟨order (selectedLevel request), graph (selectedLevel request),
      (Lax920634.ConstructionSize.size_bounds request).1,
      (Lax920634.ConstructionSize.size_bounds request).2,
      Lax920634.SubcubicConstruction.subcubic _, Lax920634.ExplicitTreewidth.linear_treewidth _⟩


end Lax263307Proofs.SourceGraphs
