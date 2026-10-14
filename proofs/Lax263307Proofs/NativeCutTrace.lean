import Lax263307Proofs.NativeCutRecords

namespace Lax263307Proofs.NativeCutTrace

open Lax263307 ComputedSeparators

theorem small {n : ℕ} (cut : Finset (Fin n) → Finset (Fin n) × Finset (Fin n))
    (fuel : ℕ) (R : Finset (Fin n)) (h : 3*R.card≤2*n) : cuts cut fuel R=[] := by
  cases fuel <;> simp [cuts,h]

theorem advance {n : ℕ} (cut : Finset (Fin n) → Finset (Fin n) × Finset (Fin n))
    (i : ℕ) (hi : i<n) (R : Finset (Fin n)) (h : ¬3*R.card≤2*n) :
    cuts cut (n-i) R=cut R::cuts cut (n-(i+1)) ((cut R).1\(cut R).2) := by
  have he : n-i=(n-(i+1))+1 := by omega
  rw [he,cuts,if_neg h]

theorem remaining_snoc {n : ℕ} (start : Finset (Fin n))
    (cs : List (Finset (Fin n) × Finset (Fin n))) (A C : Finset (Fin n)) :
    remaining start (cs++[(A,C)])=A\C := by
  simp [remaining,List.getElem_append_right]

theorem append_advance {n : ℕ} (cut : Finset (Fin n) → Finset (Fin n) × Finset (Fin n))
    (i : ℕ) (hi : i<n) (R : Finset (Fin n)) (h : ¬3*R.card≤2*n)
    (cs target : List (Finset (Fin n) × Finset (Fin n)))
    (he : cs++cuts cut (n-i) R=target) :
    (cs++[cut R])++cuts cut (n-(i+1)) ((cut R).1\(cut R).2)=target := by
  rw [advance cut i hi R h] at he
  simpa only [List.append_assoc,List.singleton_append] using he

theorem append_stop {n : ℕ} (cut : Finset (Fin n) → Finset (Fin n) × Finset (Fin n))
    (i : ℕ) (R : Finset (Fin n)) (h : 3*R.card≤2*n)
    (cs target : List (Finset (Fin n) × Finset (Fin n)))
    (he : cs++cuts cut (n-i) R=target) : cs++cuts cut (n-(i+1)) R=target := by
  simpa only [small cut _ R h] using he

end Lax263307Proofs.NativeCutTrace
