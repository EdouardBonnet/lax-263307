import Lax263307.ExhaustiveTargets
import Lax263307Proofs.RelaxationAlgebra
import Mathlib.Data.Nat.Choose.Bounds

namespace Lax263307Proofs.ExhaustiveTargets

open Lax263307.ExhaustiveTargets

/--
---
conclusion: Lax263307.ExhaustiveTargets.candidate_complete
---
Every enumerated sublist has no duplicates and length `k`. Conversely, filter
the vertex list by the desired finite set to obtain its unique ordered sublist.
-/
theorem candidate_complete (n k : ℕ) (I : Finset (Fin n)) :
    I ∈ candidates n k ↔ I.card = k := by
  constructor
  · intro hI
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hI
    obtain ⟨hsub, hlen⟩ := List.mem_sublistsLen.mp hl
    rw [List.toFinset_card_of_nodup (hsub.nodup (List.nodup_finRange n)), hlen]
  · intro hI
    let l := (List.finRange n).filter fun v => decide (v ∈ I)
    have hsub : List.Sublist l (List.finRange n) := List.filter_sublist
    have hnodup : l.Nodup := hsub.nodup (List.nodup_finRange n)
    have heq : l.toFinset = I := by ext v; simp [l]
    have hlen : l.length = k := by rw [← List.toFinset_card_of_nodup hnodup, heq, hI]
    exact List.mem_map.mpr ⟨l, List.mem_sublistsLen.mpr ⟨hsub, hlen⟩, heq⟩


/--
---
conclusion: Lax263307.ExhaustiveTargets.search_correct
---
The first successful candidate is an independent set of size `k`. If an
independent set had size at least `k` after failure, selecting a size-`k`
subset would give a successful candidate, a contradiction.

# Attribution

Bonnet–Chang, exhaustive-search rejection in Lemma 14.
-/
theorem search_correct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
    match findIndependentSet G k with
    | some I => G.IsIndepSet (I : Set (Fin n)) ∧ I.card = k
    | none => ∀ J : Finset (Fin n), G.IsIndepSet (J : Set (Fin n)) → J.card < k := by
  cases hsearch : findIndependentSet G k with
  | some I =>
    have hI : G.IsIndepSet (I : Set (Fin n)) := by
      simpa using List.find?_some hsearch
    exact ⟨hI, (Lax263307.ExhaustiveTargets.candidate_complete n k I).mp
      (List.mem_of_find?_eq_some hsearch)⟩
  | none =>
    intro J hJ
    by_contra hlarge
    obtain ⟨I, hIJ, hcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt hlarge)
    have hI : G.IsIndepSet (I : Set (Fin n)) := hJ.mono (by simpa using hIJ)
    have hmem := (Lax263307.ExhaustiveTargets.candidate_complete n k I).mpr hcard
    have hnone := List.find?_eq_none.mp hsearch I hmem
    simp [hI] at hnone

end Lax263307Proofs.ExhaustiveTargets
