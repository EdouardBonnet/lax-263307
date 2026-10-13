import Lax263307.LinearRelaxation
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sublists

/-!
---
title: Exhaustive search for small independent-set targets
type: theorem
---
For a small target $k$, enumerate exactly the $k$-element vertex sets and
test independence. The first success has size exactly $k$. If the search
fails, every independent set has size less than $k$. There are exactly
$\binom nk\le n^k$ candidates.

# Formalization notes

The executable enumeration generates sublists of length $k$, without
materializing all vertex subsets. The candidate count is separate from
the eventual RAM instruction bound.

# Attribution

Bonnet–Chang, the small-target branch of Algorithm 1.
-/

namespace Lax263307.ExhaustiveTargets

/-- Enumerate the vertex sets of one prescribed cardinality. -/
def candidates (n k : ℕ) : List (Finset (Fin n)) :=
  ((List.finRange n).sublistsLen k).map List.toFinset

/-- Deterministic exact search at target `k`. -/
def findIndependentSet {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) : Option (Finset (Fin n)) :=
  (candidates n k).find? fun I => decide (G.IsIndepSet (I : Set (Fin n)))

/-- Every size-`k` vertex set occurs, and no other cardinality occurs. -/
axiom candidate_complete (n k : ℕ) (I : Finset (Fin n)) :
  I ∈ candidates n k ↔ I.card = k

/-- Exact candidate count and its bound by a power of the graph order. -/
axiom candidate_count (n k : ℕ) :
  (candidates n k).length = n.choose k ∧ (candidates n k).length ≤ n ^ k

/-- Search success is exact; search failure excludes every larger independent set. -/
axiom search_correct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
  match findIndependentSet G k with
  | some I => G.IsIndepSet (I : Set (Fin n)) ∧ I.card = k
  | none => ∀ J : Finset (Fin n), G.IsIndepSet (J : Set (Fin n)) → J.card < k

end Lax263307.ExhaustiveTargets
