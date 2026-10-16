import Lax263307.VertexSplitting
import Mathlib.Data.List.Chain

/-!
---
title: Projecting split paths and preserving endpoint loads
type: lemma
---
A simple path of positive-capacity arcs in the split network, starting at
$u^-$ and ending at $v^+$, is the expansion of a simple original path from
$u$ to $v$. Each original vertex expands to its consecutive input/output
ports. A reverse port arc would repeat an input port, so simplicity excludes
it. Successive original vertices must therefore be graph neighbors.

For a simple original route $Q$, the expanded route traverses the capacity
arc $w^-\to w^+$ exactly once when $w$ belongs to $Q$, and zero times
otherwise. This counts both endpoints and includes singleton routes.
-/

namespace Lax263307.SplitPathProjection

open scoped NNReal NNRat
open VertexSplitting Lax455465.ProductNetwork Lax455465.ConcurrentFlow

/-- Replace each original route vertex by its consecutive two split ports. -/
def expandRoute {n : ℕ} (Q : List (Fin n)) : List (Fin (2 * n)) :=
  Q.flatMap fun v => [minus v, plus v]

/-- A positive simple split path projects to a simple original route. -/
axiom project_simple_path {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (large : ℚ≥0) (P : List (Fin (2 * n))) (u v : Fin n)
    (simple : P.Nodup)
    (chain : P.IsChain (fun a b => 0 < (splitInstance G x large).capacity a b))
    (start : P.head? = some (minus u)) (finish : P.getLast? = some (plus v)) :
    ∃ Q : List (Fin n), P = expandRoute Q ∧ Q.Nodup ∧ Q.IsChain G.Adj ∧
      Q.head? = some u ∧ Q.getLast? = some v

/-- Capacity-arc occurrence equals the original vertex-membership indicator. -/
axiom capacity_arc_count {n : ℕ} (Q : List (Fin n)) (simple : Q.Nodup) (v : Fin n) :
    ((expandRoute Q).zip (expandRoute Q).tail).count (minus v, plus v) =
      if v ∈ Q then 1 else 0

/-- Every retained positive path in a feasible split flow has such a projection. -/
axiom split_support_projection {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (large : ℚ≥0) (f : ℝ≥0) (F : PathFlow (2 * n))
    (feasible : IsConcurrentFlow .directed (splitInstance G x large).network
      (splitInstance G x large).weights f F)
    (P : List (Fin (2 * n))) (member : P ∈ F.support) (u v : Fin n)
    (start : P.head? = some (minus u)) (finish : P.getLast? = some (plus v)) :
    ∃ Q : List (Fin n), P = expandRoute Q ∧ Q.Nodup ∧ Q.IsChain G.Adj ∧
      Q.head? = some u ∧ Q.getLast? = some v

end Lax263307.SplitPathProjection
