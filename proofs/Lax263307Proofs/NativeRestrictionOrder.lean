import Lax263307Proofs.NativeMaskUnpack
import Lax263307.ComputedSeparators

namespace Lax263307Proofs.NativeRestrictionOrder

open Lax263307

def vertices {n : ℕ} (R : Finset (Fin n)) : List (Fin n) :=
  (List.finRange n).filter fun v => v∈R

theorem vertices_sort {n : ℕ} (R : Finset (Fin n)) : vertices R=R.sort (·≤·) := by
  exact ((List.sortedLT_finRange n).pairwise.filter _).sortedLT.eq_of_mem_iff R.sortedLT_sort (by simp [vertices])

theorem vertices_labels {n : ℕ} (R : Finset (Fin n)) :
    vertices R=List.ofFn (ComputedSeparators.label R) := by
  rw [vertices_sort]
  simpa only [List.finRange,List.map_ofFn,Function.comp_def,ComputedSeparators.label] using
    (Finset.listMap_orderEmbOfFin_finRange R rfl).symm

theorem length {n : ℕ} (R : Finset (Fin n)) : (vertices R).length=R.card := by
  rw [vertices_sort,Finset.length_sort]

def words {n : ℕ} (R : Finset (Fin n)) : List ℕ :=
  List.ofFn fun i : Fin R.card => (ComputedSeparators.label R i).val

def selectedPrefix {n : ℕ} (R : Finset (Fin n)) (i : ℕ) : List ℕ :=
  (((List.finRange n).take i).filter fun v => v∈R).map Fin.val

theorem prefix_zero {n : ℕ} (R : Finset (Fin n)) : selectedPrefix R 0=[] := by simp [selectedPrefix]

theorem prefix_length {n : ℕ} (R : Finset (Fin n)) (i : ℕ) : (selectedPrefix R i).length ≤ i := by
  dsimp [selectedPrefix]
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp only [List.length_take]; omega)

theorem prefix_full {n : ℕ} (R : Finset (Fin n)) : selectedPrefix R n=words R := by
  unfold selectedPrefix
  rw [List.take_of_length_le (by simp)]
  change (vertices R).map Fin.val=words R
  rw [vertices_labels,List.map_ofFn]
  rfl

theorem prefix_step {n : ℕ} (R : Finset (Fin n)) (i : ℕ) (hi : i<n) :
    selectedPrefix R (i+1)=if (⟨i,hi⟩ : Fin n)∈R then selectedPrefix R i++[i] else selectedPrefix R i := by
  unfold selectedPrefix
  rw [List.take_succ_eq_append_getElem (by simpa using hi),List.filter_append,List.map_append]
  simp only [List.getElem_finRange,Fin.cast_mk]
  split_ifs <;> simp_all

end Lax263307Proofs.NativeRestrictionOrder
