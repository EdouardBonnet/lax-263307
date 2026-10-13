import Lax263307.BalancedPartitions
import Mathlib.Tactic

namespace Lax263307Proofs.BalancedPartitions

open Lax263307.SeparatorComponents Lax263307.EdgeSublinearSeparators

theorem walk_stays {n : ℕ} {G : SimpleGraph (Fin n)} {S : Finset (Fin n)} {ι : Type}
    (P : Partition G S ι) (i : ι) {u v : ↥((↑S : Set (Fin n))ᶜ)}
    (walk : (G.induce (↑S : Set (Fin n))ᶜ).Walk u v) (hu : u.val ∈ P.vertices i) :
    v.val ∈ P.vertices i := by
  induction walk with
  | nil => exact hu
  | @cons a b c hab rest ih =>
    apply ih
    exact P.closed i a.val b.val hu b.property hab

/--
---
conclusion: Lax263307.BalancedPartitions.balanced_separator
---
Pick a vertex in each connected component and its unique partition part.
Every walk with undeleted vertices stays in that closed part, so the
component’s image is contained in it. Injective projection preserves the
component cardinality, which is bounded by the part size.
-/
theorem balanced_separator {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    {ι : Type} (P : Partition G S ι) (balanced : ∀ i, 3 * (P.vertices i).card ≤ 2 * n) :
    IsBalancedSeparator G S := by
  classical
  intro K
  obtain ⟨u, hu⟩ := K.nonempty_supp
  obtain ⟨i, hi, _⟩ := P.unique u.val u.property
  have hsubset : Subtype.val '' K.supp ⊆ (↑(P.vertices i) : Set (Fin n)) := by
    rintro v ⟨w, hw, rfl⟩
    exact walk_stays P i (K.reachable_of_mem_supp hu hw).some hi
  have hcard : K.supp.ncard ≤ (P.vertices i).card := by
    have h := Set.ncard_mono hsubset
    rw [Set.ncard_image_of_injective K.supp Subtype.val_injective, Set.ncard_coe_finset] at h
    exact h
  exact (Nat.mul_le_mul_left 3 hcard).trans (balanced i)


end Lax263307Proofs.BalancedPartitions
