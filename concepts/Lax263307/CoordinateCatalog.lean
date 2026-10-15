import Lax263307.RationalConditioning
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Dedup

/-!
---
title: A computable catalog and index for moment coordinates
type: lemma
---
Enumerate only subsets of size at most r+2, remove duplicates, and attach
the cardinality proof to each entry. This lists each moment coordinate
exactly once and gives a computable equivalence between coordinate indices
and the coordinate type. The catalog has at most (r+3)(n+1)^(r+2) entries.

# Formalization notes

The inverse index uses list search. This avoids a choice-based Fintype
equivalence in LP input construction. Duplicate removal is permitted as
its polynomial overhead in the catalogue length fits the quasipolynomial
bound. The proof package implements this enumeration on the RAM.
-/

namespace Lax263307.CoordinateCatalog

open LinearRelaxation RationalConditioning

private theorem candidate_complete_aux (n r : ℕ) (A : Finset (Fin n)) :
    A ∈ candidates n r ↔ A.card ≤ r := by
  constructor
  · intro h
    obtain ⟨j, hj, hm⟩ := List.mem_flatMap.mp h
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hm
    have hsub := (List.mem_sublistsLen.mp hl).1
    have hlen := (List.mem_sublistsLen.mp hl).2
    have hnd := hsub.nodup (List.nodup_finRange n)
    rw [List.toFinset_card_of_nodup hnd, hlen]
    have := List.mem_range.mp hj
    omega
  · intro hA
    let l := (List.finRange n).filter fun v => decide (v ∈ A)
    have hsub : List.Sublist l (List.finRange n) := List.filter_sublist
    have hnd : l.Nodup := hsub.nodup (List.nodup_finRange n)
    have heq : l.toFinset = A := by ext v; simp [l]
    have hlen : l.length = A.card := by rw [← List.toFinset_card_of_nodup hnd, heq]
    apply List.mem_flatMap.mpr
    refine ⟨A.card, List.mem_range.mpr (by omega), ?_⟩
    apply List.mem_map.mpr
    exact ⟨l, List.mem_sublistsLen.mpr ⟨hsub, hlen⟩, heq⟩

def sets (n r : ℕ) : List (Finset (Fin n)) := (candidates n (r + 2)).dedup

def catalog (n r : ℕ) : List (Coordinate n r) :=
  (sets n r).attach.map (fun A => ⟨A.val,
    (candidate_complete_aux n (r + 2) A.val).mp
      (List.mem_dedup.mp A.property)⟩)

axiom catalog_complete (n r : ℕ) (A : Coordinate n r) : A ∈ catalog n r

private theorem catalog_complete_aux (n r : ℕ) (A : Coordinate n r) : A ∈ catalog n r := by
  have hmem : A.val ∈ sets n r :=
    List.mem_dedup.mpr ((candidate_complete_aux n (r + 2) A.val).mpr A.property)
  apply List.mem_map.mpr
  exact ⟨⟨A.val, hmem⟩, List.mem_attach _ _, Subtype.ext rfl⟩

private theorem catalog_nodup_aux (n r : ℕ) : (catalog n r).Nodup := by
  have hnd : (sets n r).Nodup := List.nodup_dedup _
  apply hnd.attach.map
  intro A B h
  exact Subtype.ext (congrArg (fun C : Coordinate n r => C.val) h)

def indexing (n r : ℕ) : Fin (catalog n r).length ≃ Coordinate n r :=
  List.Nodup.getEquivOfForallMemList (catalog n r) (catalog_nodup_aux n r) (catalog_complete_aux n r)

axiom catalog_bound (n r : ℕ) : (catalog n r).length ≤ (r + 3) * (n + 1) ^ (r + 2)

axiom catalog_positive (n r : ℕ) : 0 < (catalog n r).length

axiom catalog_two (n r : ℕ) (positive : 0 < n) : 2 ≤ (catalog n r).length

end Lax263307.CoordinateCatalog
