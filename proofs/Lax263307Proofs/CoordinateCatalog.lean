import Lax263307.CoordinateCatalog
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Dedup
import Mathlib.Tactic

namespace Lax263307Proofs.CoordinateCatalog

open Lax263307.LinearRelaxation Lax263307.RationalConditioning Lax263307.CoordinateCatalog

/--
---
conclusion: Lax263307.CoordinateCatalog.catalog_complete
---
Candidate completeness and preservation of membership under duplicate removal list every coordinate.
-/
theorem catalog_complete (n r : ℕ) (A : Coordinate n r) : A ∈ catalog n r := by
  have hmem : A.val ∈ sets n r :=
    List.mem_dedup.mpr ((Lax263307.RationalConditioning.candidate_complete n (r + 2) A.val).mpr A.property)
  apply List.mem_map.mpr
  exact ⟨⟨A.val, hmem⟩, List.mem_attach _ _, Subtype.ext rfl⟩


/--
---
conclusion: Lax263307.CoordinateCatalog.catalog_bound
---
Duplicate removal cannot increase length. Apply the bounded-size candidate count at level r+2.
-/
theorem catalog_bound (n r : ℕ) : (catalog n r).length ≤ (r + 3) * (n + 1) ^ (r + 2) := by
  have hsub := List.dedup_sublist (candidates n (r + 2))
  have h := hsub.length_le.trans (Lax263307.RationalConditioning.candidate_bound n (r + 2))
  simpa only [catalog, List.length_map, List.length_attach, sets, Nat.add_assoc] using h

/--
---
conclusion: Lax263307.CoordinateCatalog.catalog_positive
---
The empty coordinate is always listed, so the catalog is nonempty.
-/
theorem catalog_positive (n r : ℕ) : 0 < (catalog n r).length := by
  have hmem := Lax263307.CoordinateCatalog.catalog_complete n r (⟨∅, by simp⟩ : Coordinate n r)
  exact List.length_pos_of_mem hmem


/--
---
conclusion: Lax263307.CoordinateCatalog.catalog_two
---
For positive graph order, the empty coordinate and a singleton coordinate are distinct catalog members.
-/
theorem catalog_two (n r : ℕ) (positive : 0 < n) : 2 ≤ (catalog n r).length := by
  let v : Fin n := ⟨0, positive⟩
  let A : Coordinate n r := ⟨∅, by simp⟩
  let B : Coordinate n r := ⟨{v}, by simp⟩
  have hne : A ≠ B := by
    intro h
    have heq : (∅ : Finset (Fin n)) = {v} := congrArg Subtype.val h
    have hv : v ∈ (∅ : Finset (Fin n)) := heq.symm ▸ Finset.mem_singleton_self v
    exact Finset.notMem_empty v hv
  have hsub : ({A, B} : Finset (Coordinate n r)) ⊆ (catalog n r).toFinset := by
    intro C hC
    simp only [Finset.mem_insert, Finset.mem_singleton] at hC
    rcases hC with rfl | rfl
    · exact List.mem_toFinset.mpr (Lax263307.CoordinateCatalog.catalog_complete n r A)
    · exact List.mem_toFinset.mpr (Lax263307.CoordinateCatalog.catalog_complete n r B)
  have hcard := Finset.card_le_card hsub
  have hpair : ({A, B} : Finset (Coordinate n r)).card = 2 := by simp [hne]
  rw [hpair] at hcard
  exact hcard.trans (List.toFinset_card_le _)

end Lax263307Proofs.CoordinateCatalog
