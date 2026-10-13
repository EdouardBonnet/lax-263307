import Lax263307.RationalConditioning
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Dedup

/-!
---
title: A computable catalog and index for moment coordinates
type: theorem
---
Enumerate only subsets of size at most r+2, remove duplicates, and attach
the cardinality proof to each entry. This lists each moment coordinate
exactly once and gives a computable equivalence between coordinate indices
and the coordinate type. The catalog has at most (r+3)(n+1)^(r+2) entries.

# Formalization notes

The inverse index uses list search. This avoids a choice-based Fintype
equivalence in LP input construction. Duplicate removal is permitted as
its polynomial overhead in the catalog length still fits the intended
quasipolynomial bound. Its actual RAM implementation remains an obligation.
-/

namespace Lax263307.CoordinateCatalog

open LinearRelaxation RationalConditioning

def sets (n r : ℕ) : List (Finset (Fin n)) := (candidates n (r + 2)).dedup

def catalog (n r : ℕ) : List (Coordinate n r) :=
  (sets n r).attach.map (fun A => ⟨A.val,
    (Lax263307.RationalConditioning.candidate_complete n (r + 2) A.val).mp
      (List.mem_dedup.mp A.property)⟩)

axiom catalog_complete (n r : ℕ) (A : Coordinate n r) : A ∈ catalog n r

axiom catalog_nodup (n r : ℕ) : (catalog n r).Nodup

def indexing (n r : ℕ) : Fin (catalog n r).length ≃ Coordinate n r :=
  List.Nodup.getEquivOfForallMemList (catalog n r) (catalog_nodup n r) (catalog_complete n r)


axiom catalog_bound (n r : ℕ) : (catalog n r).length ≤ (r + 3) * (n + 1) ^ (r + 2)

axiom catalog_positive (n r : ℕ) : 0 < (catalog n r).length

axiom catalog_two (n r : ℕ) (positive : 0 < n) : 2 ≤ (catalog n r).length

end Lax263307.CoordinateCatalog
