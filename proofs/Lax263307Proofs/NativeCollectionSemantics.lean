import Lax263307.ComputedRounding
import Lax263307.NearOracle
import Lax263307Proofs.NativeCutPieces

namespace Lax263307Proofs.NativeCollectionSemantics

open Lax263307 ComputedRounding

/-- The order used by the machine: stop at the first failed child,
otherwise accumulate successful replies as they return. -/
def loop {n : ℕ} {ι : Type} (parts : ι → Finset (Fin n)) (bound : ι → ℕ)
    (reply : ι → Option (Finset (Fin n))) : List ι → Finset (Fin n) → Result n
  | [], S => .found S
  | i::is, S => match reply i with
    | none => .cut (parts i) (bound i)
    | some I => loop parts bound reply is (S∪I)

theorem loop_find {n : ℕ} {ι : Type} [DecidableEq ι]
    (parts : ι → Finset (Fin n)) (bound : ι → ℕ) (reply : ι → Option (Finset (Fin n)))
    (order : List ι) (S : Finset (Fin n)) :
    loop parts bound reply order S =
      match order.find? (fun i => (reply i).isNone) with
      | some i => .cut (parts i) (bound i)
      | none => .found (S∪order.toFinset.biUnion (fun i => (reply i).getD ∅)) := by
  induction order generalizing S with
  | nil => simp [loop]
  | cons i is ih =>
    cases hi : reply i with
    | none => simp [loop,hi]
    | some I =>
      simp only [loop,hi,ih,List.find?_cons,Option.isNone_some,Bool.false_eq_true,if_false]
      cases hs : is.find? (fun i => (reply i).isNone) with
      | some j => simp
      | none => simp [List.toFinset_cons,Finset.biUnion_insert,hi,Finset.union_assoc]

/-- Accumulating in the given complete order returns exactly the original
functional collector, including its target-minus-one failure convention. -/
theorem realizes_collect {n : ℕ} {ι : Type} [Fintype ι] (order : List ι)
    (complete : ∀ i,i∈order) (parts : ι → Finset (Fin n)) (δ : ℚ) (k : ℕ)
    (cost : ι → ℚ) (query : ι → ℕ → Option (Finset (Fin n))) :
    loop parts (fun i => target δ (cost i)-1) (answer δ k cost query) order ∅ =
      collect order parts δ k cost query := by
  classical
  rw [loop_find]
  have hall : order.toFinset=Finset.univ := by ext i; simp [complete i]
  simp only [hall,Finset.empty_union,collect,SeparatorComponents.combine]
  rfl

theorem order_complete (q : ℕ) (i : Option (Fin q)) : i∈NearOracle.order q := by
  cases i <;> simp [NearOracle.order]

/-- The separator's stored mask list has exactly the collector's order:
the remaining part first, then the pieces of its recorded cuts. -/
theorem piece_words {n : ℕ} (cs : List (Finset (Fin n) × Finset (Fin n))) :
    NativeCutPieces.words cs = (NearOracle.order cs.length).map
      (fun i => NativeMasks.mask (ComputedSeparators.pieces cs i)) := by
  simp only [NativeCutPieces.words,NearOracle.order,List.map_cons,List.map_map,ComputedSeparators.pieces]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

end Lax263307Proofs.NativeCollectionSemantics
