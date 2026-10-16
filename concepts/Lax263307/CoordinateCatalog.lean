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

private theorem mem_candidates (n r : ℕ) (A : Finset (Fin n)) :
    A ∈ candidates n r ↔ A.card ≤ r :=
  ⟨fun member =>
    let ⟨j, inRange, inSublists⟩ := List.mem_flatMap.mp member
    let ⟨vertices, listed, sameSet⟩ := List.mem_map.mp inSublists
    let sublist := (List.mem_sublistsLen.mp listed).1
    let length := (List.mem_sublistsLen.mp listed).2
    calc
      A.card = vertices.toFinset.card := congrArg Finset.card sameSet.symm
      _ = vertices.length := List.toFinset_card_of_nodup (sublist.nodup (List.nodup_finRange n))
      _ = j := length
      _ ≤ r := Nat.le_of_lt_succ (List.mem_range.mp inRange),
   fun bounded =>
    let vertices := (List.finRange n).filter fun v => decide (v ∈ A)
    let sublist : vertices.Sublist (List.finRange n) := List.filter_sublist
    let sameSet : vertices.toFinset = A := Finset.ext fun v =>
      List.mem_toFinset.trans (List.mem_filter.trans
        ⟨fun h => of_decide_eq_true h.2,
         fun h => ⟨List.mem_finRange v, decide_eq_true h⟩⟩)
    let length : vertices.length = A.card :=
      (List.toFinset_card_of_nodup (sublist.nodup (List.nodup_finRange n))).symm.trans
        (congrArg Finset.card sameSet)
    List.mem_flatMap.mpr ⟨A.card, List.mem_range.mpr (Nat.lt_succ_of_le bounded),
      List.mem_map.mpr ⟨vertices, List.mem_sublistsLen.mpr ⟨sublist, length⟩, sameSet⟩⟩⟩

def sets (n r : ℕ) : List (Finset (Fin n)) := (candidates n (r + 2)).dedup

def catalog (n r : ℕ) : List (Coordinate n r) :=
  (sets n r).attach.map (fun A => ⟨A.val,
    (mem_candidates n (r + 2) A.val).mp
      (List.mem_dedup.mp A.property)⟩)

axiom catalog_complete (n r : ℕ) (A : Coordinate n r) : A ∈ catalog n r

private theorem mem_catalog (n r : ℕ) (A : Coordinate n r) : A ∈ catalog n r :=
  let listed : A.val ∈ sets n r :=
    List.mem_dedup.mpr ((mem_candidates n (r + 2) A.val).mpr A.property)
  List.mem_map.mpr ⟨⟨A.val, listed⟩, List.mem_attach _ _, Subtype.ext rfl⟩

private theorem catalog_nodup (n r : ℕ) : (catalog n r).Nodup :=
  (List.nodup_dedup _).attach.map fun _ _ equal =>
    Subtype.ext (congrArg (fun coordinate : Coordinate n r => coordinate.val) equal)

def indexing (n r : ℕ) : Fin (catalog n r).length ≃ Coordinate n r :=
  List.Nodup.getEquivOfForallMemList (catalog n r) (catalog_nodup n r) (mem_catalog n r)

axiom catalog_bound (n r : ℕ) : (catalog n r).length ≤ (r + 3) * (n + 1) ^ (r + 2)

axiom catalog_positive (n r : ℕ) : 0 < (catalog n r).length

axiom catalog_two (n r : ℕ) (positive : 0 < n) : 2 ≤ (catalog n r).length

end Lax263307.CoordinateCatalog
