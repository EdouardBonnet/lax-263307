import Lax263307.ConditioningDistribution
import Lax263307.EntropyGap
import Lax263307.EntropyBounds
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.FinRange
import Mathlib.Data.Finset.Card

/-!
---
title: Rational conditioning and its candidate list
type: lemma
---
A rational conditioning test checks positivity of a moment and the
corresponding edge-product inequality using exact arithmetic. Its search
examines vertex sets of size at most $r$ in a fixed order.

The candidate list contains exactly those sets and has at most
$(r+1)(n+1)^r$ entries.

# Formalization notes

Candidates are generated as sublists of each prescribed length, rather
than by materializing the full power set. The heavy-conditioning search
uses the same rational coordinates and candidate list.
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

end Lax263307.RationalConditioning
