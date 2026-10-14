import Lax263307Proofs.NativeMomentAccess
import Lax263307.HeavyRationalConditioning
import Mathlib.Data.List.Find

namespace Lax263307Proofs.NativeConditioningOrder

open Lax263307 RationalConditioning HeavyRationalConditioning NativeCatalogMetadata

def test {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k p : ℕ)
    (y : RationalVector n r) (A : Finset (Fin n)) : Bool := decide (A.card≤r ∧ HeavyPasses G k p y A)

def accepted {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k p : ℕ)
    (y : RationalVector n r) (i : Fin (N n r)) : Bool := test G k p y (atIndex n r i)

def first {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k p : ℕ)
    (y : RationalVector n r) : ℕ := (List.finRange (N n r)).findIdx (accepted G k p y)

theorem sequence (n r : ℕ) : (List.finRange (N n r)).map (atIndex n r)=candidates n (r+2) := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i<N n r
  · rw [List.getElem?_eq_getElem (by simpa using hi),List.getElem_map,List.getElem_finRange,
      NativeCatalogOrder.catalog_index n r ⟨i,hi⟩]
    rfl
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hi),List.getElem?_eq_none]
    rw [←NativeCatalogOrder.catalog_length]
    exact Nat.le_of_not_gt hi

theorem filtered_find {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k p : ℕ) (y : RationalVector n r) :
    (candidates n (r+2)).find? (test G k p y)=findHeavyConditioning G k p y := by
  have htail (s : ℕ) (hr : r<s) : (ExhaustiveTargets.candidates n s).find? (test G k p y)=none := by
    apply List.find?_eq_none.mpr
    intro A hA
    have hc := NativeCatalogOrder.candidate_card n s A hA
    simp only [test,decide_eq_true_eq]
    intro h
    omega
  have hfront : (candidates n r).find? (test G k p y)=findHeavyConditioning G k p y := by
    apply List.find?_congr
    intro A hA
    have hc := (Lax263307.RationalConditioning.candidate_complete n r A).mp hA
    simp only [test,hc,true_and]
  have hsplit : candidates n (r+2)=(candidates n r++ExhaustiveTargets.candidates n (r+1))++ExhaustiveTargets.candidates n (r+2) := by
    exact (NativeCatalogOrder.all_candidates_succ n (r+1)).trans
      (congrArg (fun xs => xs++ExhaustiveTargets.candidates n (r+2)) (NativeCatalogOrder.all_candidates_succ n r))
  rw [hsplit,List.find?_append,List.find?_append,htail (r+1) (by omega),htail (r+2) (by omega),hfront]
  simp

theorem selected {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k p : ℕ) (y : RationalVector n r) :
    ((List.finRange (N n r)).find? (accepted G k p y)).map (atIndex n r)=findHeavyConditioning G k p y := by
  change ((List.finRange (N n r)).find? ((test G k p y) ∘ atIndex n r)).map (atIndex n r)=_
  rw [←List.find?_map,sequence,filtered_find]

theorem first_le {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k p : ℕ) (y : RationalVector n r) : first G k p y≤N n r := by
  simpa only [first,List.length_finRange] using
    (List.findIdx_le_length (p:=accepted G k p y) (xs:=List.finRange (N n r)))

theorem before {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k p : ℕ) (y : RationalVector n r) (i : Fin (N n r)) (hi : i.val<first G k p y) :
    accepted G k p y i=false := by
  simpa only [List.getElem_finRange,Fin.cast_mk,Fin.eta] using List.not_of_lt_findIdx hi

theorem at_first {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k p : ℕ) (y : RationalVector n r) (hf : first G k p y<N n r) :
    accepted G k p y ⟨first G k p y,hf⟩=true := by
  have hh := List.findIdx_getElem (p:=accepted G k p y) (xs:=List.finRange (N n r))
    (w:=by simpa only [first,List.length_finRange] using hf)
  simpa only [first,List.getElem_finRange,Fin.cast_mk] using hh

end Lax263307Proofs.NativeConditioningOrder
