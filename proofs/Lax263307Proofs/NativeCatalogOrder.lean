import Lax263307Proofs.NativeExhaustive
import Lax263307.CoordinateCatalog
import Mathlib.Data.List.Sort

namespace Lax263307Proofs.NativeCatalogOrder

open Lax263307

theorem sublist_toFinset_injective (n : ℕ) (xs ys : List (Fin n))
    (hx : xs.Sublist (List.finRange n)) (hy : ys.Sublist (List.finRange n))
    (he : xs.toFinset=ys.toFinset) : xs=ys := by
  have hs : (List.finRange n).Pairwise (fun u v : Fin n => u<v) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simpa only [List.getElem_finRange, Fin.lt_def, Fin.val_cast] using hij
  apply (hs.sublist hx).eq_of_mem_iff (hs.sublist hy)
  intro v
  have hh := congrArg (fun I : Finset (Fin n) => v∈I) he
  simpa only [List.mem_toFinset] using Iff.of_eq hh

theorem candidates_nodup (n k : ℕ) : (ExhaustiveTargets.candidates n k).Nodup := by
  exact List.Nodup.map_on (by
    intro xs hx ys hy he
    exact sublist_toFinset_injective n xs ys (List.mem_sublistsLen.mp hx).1
      (List.mem_sublistsLen.mp hy).1 he)
    (List.nodup_sublistsLen k (List.nodup_finRange n))

theorem candidate_card (n k : ℕ) (I : Finset (Fin n)) (hI : I∈ExhaustiveTargets.candidates n k) :
    I.card=k := by
  obtain ⟨xs,hxs,rfl⟩ := List.mem_map.mp hI
  obtain ⟨hsub,hlen⟩ := List.mem_sublistsLen.mp hxs
  rw [List.toFinset_card_of_nodup (hsub.nodup (List.nodup_finRange n)),hlen]

theorem all_candidates_nodup (n R : ℕ) : (RationalConditioning.candidates n R).Nodup := by
  change ((List.range (R+1)).flatMap (fun k => ExhaustiveTargets.candidates n k)).Nodup
  rw [List.nodup_flatMap]
  refine ⟨fun k _ => candidates_nodup n k,?_⟩
  apply List.nodup_range.imp
  intro k l hne I hI hJ
  exact hne ((candidate_card n k I hI).symm.trans (candidate_card n l I hJ))

theorem sets_eq (n r : ℕ) : CoordinateCatalog.sets n r=RationalConditioning.candidates n (r+2) := by
  exact List.dedup_eq_self.mpr (all_candidates_nodup n (r+2))

theorem catalog_values (n r : ℕ) :
    (CoordinateCatalog.catalog n r).map Subtype.val=RationalConditioning.candidates n (r+2) := by
  rw [CoordinateCatalog.catalog,List.map_map]
  simpa only [Function.comp_def,List.attach_map_subtype_val] using sets_eq n r

theorem catalog_length (n r : ℕ) :
    (CoordinateCatalog.catalog n r).length=(RationalConditioning.candidates n (r+2)).length := by
  simpa only [List.length_map] using congrArg List.length (catalog_values n r)

theorem catalog_index (n r : ℕ) (j : Fin (CoordinateCatalog.catalog n r).length) :
    (RationalConditioning.candidates n (r+2))[j.val]?=some (CoordinateCatalog.indexing n r j).val := by
  rw [←catalog_values,List.getElem?_map,List.getElem?_eq_getElem j.isLt]
  rfl

theorem candidate_block {α : Type*} (n k : ℕ) (f : Finset (Fin n) → α) :
    List.ofFn (fun j : Fin (n.choose k) => f (NativeExhaustive.candidate n k j.val))=
      (ExhaustiveTargets.candidates n k).map f := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i<n.choose k
  · have hic : i<(ExhaustiveTargets.candidates n k).length := by
      simpa only [ExhaustiveTargets.candidates,List.length_map,List.length_sublistsLen,List.length_finRange] using hi
    rw [List.getElem?_ofFn,dif_pos hi,List.getElem?_map,NativeExhaustive.candidate_get n k i hi]
    rfl
  · rw [List.getElem?_ofFn,dif_neg hi,List.getElem?_eq_none]
    simpa only [ExhaustiveTargets.candidates,List.length_map,List.length_sublistsLen,List.length_finRange] using Nat.le_of_not_gt hi

theorem all_candidates_length (n R : ℕ) :
    (RationalConditioning.candidates n R).length=((List.range (R+1)).map fun k => n.choose k).sum := by
  simp [RationalConditioning.candidates,List.length_flatMap,List.length_sublistsLen]

theorem all_candidates_succ (n R : ℕ) :
    RationalConditioning.candidates n (R+1)=
      RationalConditioning.candidates n R++ExhaustiveTargets.candidates n (R+1) := by
  unfold RationalConditioning.candidates ExhaustiveTargets.candidates
  rw [List.range_succ,List.flatMap_append]
  simp

theorem dimension_sum (n r : ℕ) :
    (CoordinateCatalog.catalog n r).length=((List.range (r+3)).map fun k => n.choose k).sum := by
  rw [catalog_length,all_candidates_length]

end Lax263307Proofs.NativeCatalogOrder
