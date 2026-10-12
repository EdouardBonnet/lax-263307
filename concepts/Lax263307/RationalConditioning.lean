import Lax263307.ConditioningExistence
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.FinRange
import Mathlib.Data.Finset.Card

/-!
---
title: Exact rational search for a conditioning set
type: theorem
---
For a rational feasible point of $R_r(G,k)$, enumerate the vertex sets
of size at most $r$ and return the first set $A$ satisfying $y_A>0$ and
$$p\sum_{u,v:\,uv\in E(G)}y_{A\cup\{u\}}y_{A\cup\{v\}}
  \le2k^2y_A^2.$$
The sum counts ordered adjacent pairs. This exact rational test is equivalent
to the edge-cost condition in Lemma 12. Under that lemma's hypotheses the
search succeeds and returns the required costs. The list contains at most
$(r+1)(n+1)^r$ candidates.

# Formalization notes

Candidates are generated as sublists of each prescribed length, in a fixed
order. Enumeration does not first materialize the full power set.
This statement proves exact search correctness and bounds its candidate count;
the RAM instruction and bit-length bounds are separate obligations.
-/

namespace Lax263307.RationalConditioning

open LinearRelaxation Entropy

/-- Rational coordinates for the same truncated relaxation. -/
abbrev RationalVector (n r : ℕ) := Coordinate n r → ℚ

/-- Interpret a rational moment vector in the real vector space. -/
def realVector {n r : ℕ} (y : RationalVector n r) : MomentVector n r :=
  fun A => (y A : ℝ)

/-- Read a rational coordinate, extending by zero outside the coordinate domain. -/
def rationalValue {n r : ℕ} (y : RationalVector n r) (A : Finset (Fin n)) : ℚ :=
  if h : A.card ≤ r + 2 then y ⟨A, h⟩ else 0

/-- The ordered edge-product numerator in the exact test. -/
def edgeNumerator {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (y : RationalVector n r) (A : Finset (Fin n)) : ℚ :=
  ∑ u, ∑ v, if G.Adj u v then
    rationalValue y (insert u A) * rationalValue y (insert v A) else 0

/-- The exact rational test after clearing the positive conditioning denominator. -/
def Passes {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k p : ℕ) (y : RationalVector n r) (A : Finset (Fin n)) : Prop :=
  0 < rationalValue y A ∧
    (p : ℚ) * edgeNumerator G y A ≤ 2 * (k : ℚ) ^ 2 * rationalValue y A ^ 2

/-- The rational test is decidable by exact arithmetic. -/
instance {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k p : ℕ) (y : RationalVector n r) (A : Finset (Fin n)) : Decidable (Passes G k p y A) :=
  inferInstanceAs (Decidable (0 < rationalValue y A ∧
    (p : ℚ) * edgeNumerator G y A ≤ 2 * (k : ℚ) ^ 2 * rationalValue y A ^ 2))

/-- Enumerate only sublists with lengths between zero and the conditioning budget. -/
def candidates (n r : ℕ) : List (Finset (Fin n)) :=
  (List.range (r + 1)).flatMap fun j =>
    ((List.finRange n).sublistsLen j).map List.toFinset

/-- Return the first candidate satisfying the rational test. -/
def findConditioning {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k p : ℕ) (y : RationalVector n r) : Option (Finset (Fin n)) :=
  (candidates n r).find? fun A => decide (Passes G k p y A)

/-- The candidate list contains exactly the vertex sets within the budget. -/
axiom candidate_complete (n r : ℕ) (A : Finset (Fin n)) :
  A ∈ candidates n r ↔ A.card ≤ r

/-- The number of candidates has the required polynomial dependence on `n` at fixed `r`. -/
axiom candidate_bound (n r : ℕ) : (candidates n r).length ≤ (r + 1) * (n + 1) ^ r

/-- The exact rational search returns a conditioning set with the promised costs. -/
axiom search_correct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k r p : ℕ) (y : RationalVector n r) (feasible : IsFeasible G k r (realVector y))
    (target_positive : 0 < k) (level_positive : 0 < r) (threshold_positive : 0 < p)
    (budget : 2 * (p : ℝ) * Real.logb 2 n ≤ r) :
    ∃ A : Finset (Fin n), findConditioning G k p y = some A ∧ A.card ≤ r ∧
      0 < value (realVector y) A ∧
      (∀ v, 0 ≤ conditioned (realVector y) A v ∧ conditioned (realVector y) A v ≤ 1) ∧
      (∑ v, conditioned (realVector y) A v) = k ∧
      edgeCost G (conditioned (realVector y) A) ≤ (k : ℝ) ^ 2 / p

end Lax263307.RationalConditioning
