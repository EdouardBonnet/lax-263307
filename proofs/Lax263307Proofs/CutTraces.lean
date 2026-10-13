import Lax263307.CutTraces
import Mathlib.Tactic

namespace Lax263307Proofs.CutTraces

open Lax263307.SeparatorComponents Lax263307.EdgeSublinearSeparators Lax263307.CutTraces

theorem right_subset {n q : ℕ} {G : SimpleGraph (Fin n)} {start : Finset (Fin n)}
    (T : Trace G start q) (i : ℕ) (hi : i < q) : T.right i ⊆ T.remaining i := by
  rw [← T.cover i hi]
  exact Finset.subset_union_right

theorem next_sdiff {n q : ℕ} {G : SimpleGraph (Fin n)} {start : Finset (Fin n)}
    (T : Trace G start q) (i : ℕ) (hi : i < q) : T.remaining (i + 1) = T.remaining i \ T.right i := by
  rw [T.next i hi, ← T.cover i hi]
  ext v
  simp only [Finset.mem_sdiff, Finset.mem_union]
  tauto

theorem remaining_formula {n q : ℕ} {G : SimpleGraph (Fin n)} {start : Finset (Fin n)}
    (T : Trace G start q) (j : ℕ) (hj : j ≤ q) :
    T.remaining j = start \ (Finset.range j).biUnion T.right := by
  revert hj
  induction j with
  | zero => intro _; simp [T.initial]
  | succ j ih =>
    intro hj
    rw [next_sdiff T j (by omega), ih (by omega), Finset.range_add_one, Finset.biUnion_insert]
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto

theorem remaining_mono {n q : ℕ} {G : SimpleGraph (Fin n)} {start : Finset (Fin n)}
    (T : Trace G start q) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ q) :
    T.remaining j ⊆ T.remaining i := by
  rw [remaining_formula T j hj, remaining_formula T i (by omega)]
  intro v hv
  have hv := Finset.mem_sdiff.mp hv
  apply Finset.mem_sdiff.mpr
  refine ⟨hv.1, ?_⟩
  intro hi
  obtain ⟨k, hk, hkv⟩ := Finset.mem_biUnion.mp hi
  exact hv.2 (Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr
    (lt_of_lt_of_le (Finset.mem_range.mp hk) hij), hkv⟩)

theorem right_pairwise {n q : ℕ} {G : SimpleGraph (Fin n)} {start : Finset (Fin n)}
    (T : Trace G start q) : Pairwise fun i j : Fin q => Disjoint (T.right i) (T.right j) := by
  have earlier (i j : Fin q) (hij : i.val < j.val) : Disjoint (T.right i) (T.right j) := by
    apply Finset.disjoint_left.mpr
    intro v hvi hvj
    have hv := remaining_mono T (i.val + 1) j.val (by omega) j.isLt.le
      (right_subset T j j.isLt hvj)
    rw [next_sdiff T i i.isLt] at hv
    exact (Finset.mem_sdiff.mp hv).2 hvi
  intro i j hne
  have hv : i.val ≠ j.val := by intro h; exact hne (Fin.ext h)
  rcases lt_or_gt_of_ne hv with hij | hji
  · exact earlier i j hij
  · exact (earlier j i hji).symm

theorem step_bound {n q : ℕ} {G : SimpleGraph (Fin n)} {start : Finset (Fin n)}
    (T : Trace G start q) : q ≤ start.card := by
  have hcard : ∀ j ≤ q, j + (T.remaining j).card ≤ start.card := by
    intro j
    induction j with
    | zero => intro _; simp [T.initial]
    | succ j ih =>
      intro hj
      have hprev := ih (by omega)
      have hB : 0 < (T.right j).card := Finset.card_pos.mpr (T.nonempty j (by omega))
      have hsum := Finset.card_sdiff_add_card_eq_card (right_subset T j (by omega))
      rw [← next_sdiff T j (by omega)] at hsum
      omega
  have h := hcard q (le_refl _)
  omega

theorem final_disjoint {n q : ℕ} {G : SimpleGraph (Fin n)} {start : Finset (Fin n)}
    (T : Trace G start q) (i : Fin q) : Disjoint (T.remaining q) (T.right i) := by
  apply Finset.disjoint_left.mpr
  intro v hv hvi
  have h := remaining_mono T (i.val + 1) q (by omega) (le_refl _) hv
  rw [next_sdiff T i i.isLt] at h
  exact (Finset.mem_sdiff.mp h).2 hvi

theorem parts_outside {n q : ℕ} {G : SimpleGraph (Fin n)} {start : Finset (Fin n)}
    (T : Trace G start q) (i : Option (Fin q)) (v : Fin n) (hv : v ∈ parts T i) : v ∉ separator T := by
  classical
  intro hs
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hs
  have hjB := (Finset.mem_inter.mp hj).2
  cases i with
  | none => exact Finset.disjoint_left.mp (final_disjoint T j) hv hjB
  | some i =>
    have hi := Finset.mem_sdiff.mp hv
    by_cases he : i = j
    · subst j
      exact hi.2 (Finset.mem_inter.mp hj).1
    · exact Finset.disjoint_left.mp (right_pairwise T he) hi.1 hjB

theorem parts_unique {n q : ℕ} {G : SimpleGraph (Fin n)}
    (T : Trace G Finset.univ q) (v : Fin n) (hs : v ∉ separator T) :
    ∃! i, v ∈ parts T i := by
  classical
  by_cases hex : ∃ i : Fin q, v ∈ T.right i
  · obtain ⟨i, hi⟩ := hex
    have hnotA : v ∉ T.left i := by
      intro hv
      exact hs (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_inter.mpr ⟨hv, hi⟩⟩)
    refine ⟨some i, Finset.mem_sdiff.mpr ⟨hi, hnotA⟩, ?_⟩
    intro j hj
    cases j with
    | none => exact (Finset.disjoint_left.mp (final_disjoint T i) hj hi).elim
    | some j =>
      have hji : j = i := by
        by_contra h
        exact Finset.disjoint_left.mp (right_pairwise T h) (Finset.mem_sdiff.mp hj).1 hi
      exact congrArg some hji
  · have hv : v ∈ T.remaining q := by
      rw [remaining_formula T q (le_refl _)]
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      intro h
      obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp h
      exact hex ⟨⟨i, Finset.mem_range.mp hi⟩, hvi⟩
    refine ⟨none, hv, ?_⟩
    intro i hi
    cases i with
    | none => rfl
    | some i => exact (hex ⟨i, (Finset.mem_sdiff.mp hi).1⟩).elim

theorem no_cross_parts {n q : ℕ} {G : SimpleGraph (Fin n)} {start : Finset (Fin n)}
    (T : Trace G start q) (i j : Option (Fin q)) (different : i ≠ j)
    (u v : Fin n) (hu : u ∈ parts T i) (hv : v ∈ parts T j) : ¬G.Adj u v := by
  cases i with
  | none =>
    cases j with
    | none => exact (different rfl).elim
    | some j =>
      have hu' : u ∈ T.left j \ T.right j := by
        rw [← T.next j j.isLt]
        exact remaining_mono T (j.val + 1) q (by omega) (le_refl _) hu
      exact T.separated j j.isLt u hu' v hv
  | some i =>
    cases j with
    | none =>
      have hv' : v ∈ T.left i \ T.right i := by
        rw [← T.next i i.isLt]
        exact remaining_mono T (i.val + 1) q (by omega) (le_refl _) hv
      exact fun h => T.separated i i.isLt v hv' u hu h.symm
    | some j =>
      have hne : i.val ≠ j.val := by intro h; exact different (congrArg some (Fin.ext h))
      rcases lt_or_gt_of_ne hne with hij | hji
      · have hv' : v ∈ T.left i \ T.right i := by
          rw [← T.next i i.isLt]
          exact remaining_mono T (i.val + 1) j (by omega) j.isLt.le
            (right_subset T j j.isLt (Finset.mem_sdiff.mp hv).1)
        exact fun h => T.separated i i.isLt v hv' u hu h.symm
      · have hu' : u ∈ T.left j \ T.right j := by
          rw [← T.next j j.isLt]
          exact remaining_mono T (j.val + 1) i (by omega) i.isLt.le
            (right_subset T i i.isLt (Finset.mem_sdiff.mp hu).1)
        exact T.separated j j.isLt u hu' v hv

def partition {n q : ℕ} {G : SimpleGraph (Fin n)} (T : Trace G Finset.univ q) :
    Partition G (separator T) (Option (Fin q)) where
  vertices := parts T
  outside := parts_outside T
  unique := parts_unique T
  closed := by
    intro i u v hu hv huv
    obtain ⟨j, hj, _⟩ := parts_unique T v hv
    have hji : j = i := by
      by_contra h
      exact no_cross_parts T i j (Ne.symm h) u v hu hj huv
    simpa [hji] using hj

/--
---
conclusion: Lax263307.CutTraces.trace_correct
---
The remainder equals the initial set minus previously discarded shores.
Hence discarded shores are disjoint and their nonemptiness bounds the
number of cuts. The exclusive pieces and final remainder partition all
undeleted vertices without cross edges. Their size bounds certify balance;
the cumulative cut-cost theorem gives the separator budget.
-/
theorem trace_correct {n q : ℕ} (G : SimpleGraph (Fin n)) (T : Trace G Finset.univ q)
    (finished : 3 * (T.remaining q).card ≤ 2 * n)
    (x : Fin n → ℝ) (nonnegative : ∀ v, 0 ≤ x v) (ρ γ : ℝ) (hρ : 0 ≤ ρ) (hγ : 0 < γ)
    (each_cut : ∀ i < q, Lax263307.RepeatedCutAccounting.cost x (T.left i ∩ T.right i) ≤
      4 * ρ * (T.left i).card * (T.right i).card / γ) :
    q ≤ n ∧ IsBalancedSeparator G (separator T) ∧
      Lax263307.RepeatedCutAccounting.cost x (separator T) ≤ 4 * ρ * (n : ℝ) ^ 2 / γ := by
  classical
  refine ⟨by simpa using step_bound T, ?_, ?_⟩
  · apply Lax263307.BalancedPartitions.balanced_separator G (separator T) (partition T)
    intro i
    cases i with
    | none => exact finished
    | some i =>
      have h := T.small_piece i i.isLt
      have hr : (T.remaining i).card ≤ n := by simpa using Finset.card_le_univ (T.remaining i)
      change 3 * (T.right i \ T.left i).card ≤ 2 * n
      omega
  · exact Lax263307.RepeatedCutAccounting.total_cut_cost x nonnegative
      (fun i : Fin q => T.left i) (fun i : Fin q => T.right i) (right_pairwise T) ρ γ hρ hγ
        (fun i => each_cut i i.isLt)

def emptyTrace {n : ℕ} (G : SimpleGraph (Fin n)) (start : Finset (Fin n)) : Trace G start 0 where
  remaining := fun _ => start
  left := fun _ => ∅
  right := fun _ => ∅
  initial := rfl
  cover := by intro i hi; omega
  next := by intro i hi; omega
  nonempty := by intro i hi; omega
  small_piece := by intro i hi; omega
  separated := by intro i hi; omega

def prepend {n q : ℕ} {G : SimpleGraph (Fin n)} {start : Finset (Fin n)}
    (A B : Finset (Fin n)) (cover : A ∪ B = start) (nonempty : B.Nonempty)
    (small : 2 * (B \ A).card ≤ start.card)
    (separated : ∀ u ∈ A \ B, ∀ v ∈ B \ A, ¬G.Adj u v)
    (T : Trace G (A \ B) q) : Trace G start (q + 1) where
  remaining | 0 => start | i + 1 => T.remaining i
  left | 0 => A | i + 1 => T.left i
  right | 0 => B | i + 1 => T.right i
  initial := rfl
  cover := by intro i hi; cases i with
    | zero => exact cover
    | succ i => exact T.cover i (by omega)
  next := by intro i hi; cases i with
    | zero => exact T.initial
    | succ i => exact T.next i (by omega)
  nonempty := by intro i hi; cases i with
    | zero => exact nonempty
    | succ i => exact T.nonempty i (by omega)
  small_piece := by intro i hi; cases i with
    | zero => exact small
    | succ i => exact T.small_piece i (by omega)
  separated := by intro i hi; cases i with
    | zero => exact separated
    | succ i => exact T.separated i (by omega)

theorem exists_trace {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → ℝ) (ρ γ : ℝ)
    (oracle : ∀ R : Finset (Fin n), 2 * n < 3 * R.card →
      ∃ A B : Finset (Fin n), A ∪ B = R ∧ B.Nonempty ∧ 2 * (B \ A).card ≤ R.card ∧
        (∀ u ∈ A \ B, ∀ v ∈ B \ A, ¬G.Adj u v) ∧
        Lax263307.RepeatedCutAccounting.cost x (A ∩ B) ≤ 4 * ρ * A.card * B.card / γ)
    (start : Finset (Fin n)) :
    ∃ q, ∃ T : Trace G start q, 3 * (T.remaining q).card ≤ 2 * n ∧
      ∀ i < q, Lax263307.RepeatedCutAccounting.cost x (T.left i ∩ T.right i) ≤
        4 * ρ * (T.left i).card * (T.right i).card / γ := by
  have produce : ∀ size, ∀ R : Finset (Fin n), R.card = size →
      ∃ q, ∃ T : Trace G R q, 3 * (T.remaining q).card ≤ 2 * n ∧
        ∀ i < q, Lax263307.RepeatedCutAccounting.cost x (T.left i ∩ T.right i) ≤
          4 * ρ * (T.left i).card * (T.right i).card / γ := by
    intro size
    induction size using Nat.strong_induction_on with
    | h size ih =>
      intro R hR
      by_cases hstop : 3 * R.card ≤ 2 * n
      · refine ⟨0, emptyTrace G R, hstop, ?_⟩
        intro i hi
        omega
      · obtain ⟨A, B, hcover, hnonempty, hsmall, hsep, hcost⟩ := oracle R (lt_of_not_ge hstop)
        have hBsub : B ⊆ R := by rw [← hcover]; exact Finset.subset_union_right
        have hnext : A \ B = R \ B := by
          rw [← hcover]
          ext v
          simp only [Finset.mem_sdiff, Finset.mem_union]
          tauto
        have hcount := Finset.card_sdiff_add_card_eq_card hBsub
        have hpositive := Finset.card_pos.mpr hnonempty
        have hdecrease : (A \ B).card < size := by rw [hnext]; omega
        obtain ⟨q, T, hfinished, hcosts⟩ := ih (A \ B).card hdecrease (A \ B) rfl
        refine ⟨q + 1, prepend A B hcover hnonempty hsmall hsep T, hfinished, ?_⟩
        intro i hi
        cases i with
        | zero => exact hcost
        | succ i => exact hcosts i (by omega)
  exact produce start.card start rfl

/--
---
conclusion: Lax263307.CutTraces.light_separator_from_oracle
---
Induct on remainder cardinality. A large remainder receives an oracle
cut whose nonempty right shore strictly reduces it; prepend that cut to
the recursively constructed trace. A small remainder stops immediately.
Apply the proved trace analysis to obtain the final separator and cost.
-/
theorem light_separator_from_oracle {n : ℕ} (G : SimpleGraph (Fin n))
    (x : Fin n → ℝ) (nonnegative : ∀ v, 0 ≤ x v) (ρ γ : ℝ) (hρ : 0 ≤ ρ) (hγ : 0 < γ)
    (oracle : ∀ R : Finset (Fin n), 2 * n < 3 * R.card →
      ∃ A B : Finset (Fin n), A ∪ B = R ∧ B.Nonempty ∧ 2 * (B \ A).card ≤ R.card ∧
        (∀ u ∈ A \ B, ∀ v ∈ B \ A, ¬G.Adj u v) ∧
        Lax263307.RepeatedCutAccounting.cost x (A ∩ B) ≤ 4 * ρ * A.card * B.card / γ) :
    ∃ q, ∃ T : Trace G Finset.univ q, q ≤ n ∧ IsBalancedSeparator G (separator T) ∧
      Lax263307.RepeatedCutAccounting.cost x (separator T) ≤ 4 * ρ * (n : ℝ) ^ 2 / γ := by
  obtain ⟨q, T, hfinished, hcosts⟩ := exists_trace G x ρ γ oracle Finset.univ
  exact ⟨q, T, Lax263307.CutTraces.trace_correct G T hfinished x nonnegative ρ γ hρ hγ hcosts⟩


end Lax263307Proofs.CutTraces
