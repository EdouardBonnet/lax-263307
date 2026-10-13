import Lax263307.SplitPathProjection
import Lax263307Proofs.VertexSplitting

namespace Lax263307Proofs.SplitPathProjection

open scoped NNReal NNRat
open Lax263307.VertexSplitting Lax263307.SplitPathProjection
open Lax263307Proofs.VertexSplitting
open Lax455465.ProductNetwork Lax455465.ConcurrentFlow

theorem minus_ne_plus {n : ℕ} (u v : Fin n) : minus u ≠ plus v := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [minus, plus] at hv
  omega

theorem plus_injective (n : ℕ) : Function.Injective (plus (n := n)) := by
  intro u v h
  have hv := congrArg Fin.val h
  apply Fin.ext
  dsimp [plus] at hv
  omega

theorem minus_mem_expand {n : ℕ} (Q : List (Fin n)) (u : Fin n) (hu : u ∈ Q) :
    minus u ∈ expandRoute Q := by
  exact List.mem_flatMap.mpr ⟨u, hu, by simp⟩

theorem minus_injective (n : ℕ) : Function.Injective (minus (n := n)) := by
  intro u v h
  simpa only [original_minus] using congrArg original h

theorem capacity_arc_count_count {n : ℕ} (Q : List (Fin n)) (v : Fin n) :
    ((expandRoute Q).zip (expandRoute Q).tail).count (minus v, plus v) = Q.count v := by
  induction Q with
  | nil => simp [expandRoute]
  | cons u Q ih =>
    by_cases huv : u = v
    · subst u
      cases Q with
      | nil => simp [expandRoute]
      | cons w Q =>
        have hcross : (plus v, minus w) ≠ (minus v, plus v) := by
          intro he
          exact minus_ne_plus v v (congrArg Prod.fst he).symm
        change ((minus v, plus v) :: (plus v, minus w) ::
          ((expandRoute (w :: Q)).zip (expandRoute (w :: Q)).tail)).count (minus v, plus v) = _
        rw [List.count_cons_self, List.count_cons_of_ne hcross, ih, List.count_cons_self]
    · have hfirst : (minus u, plus u) ≠ (minus v, plus v) := by
        intro he
        exact huv (minus_injective n (congrArg Prod.fst he))
      cases Q with
      | nil => simp [expandRoute, hfirst, huv]
      | cons w Q =>
        have hcross : (plus u, minus w) ≠ (minus v, plus v) := by
          intro he
          exact minus_ne_plus v u (congrArg Prod.fst he).symm
        change ((minus u, plus u) :: (plus u, minus w) ::
          ((expandRoute (w :: Q)).zip (expandRoute (w :: Q)).tail)).count (minus v, plus v) = _
        rw [List.count_cons_of_ne hfirst, List.count_cons_of_ne hcross, ih,
          List.count_cons_of_ne huv]

/--
---
conclusion: Lax263307.SplitPathProjection.capacity_arc_count
---
The expanded list contains one forward capacity arc per occurrence of the
original vertex. Cross arcs join output ports to input ports and cannot be
capacity arcs. On a simple route, a vertex occurs either once or not at all.

# Attribution

Bonnet–Chang, endpoint-inclusive load accounting in Lemma 7.
-/
theorem capacity_arc_count {n : ℕ} (Q : List (Fin n)) (simple : Q.Nodup) (v : Fin n) :
    ((expandRoute Q).zip (expandRoute Q).tail).count (minus v, plus v) =
      if v ∈ Q then 1 else 0 := by
  rw [capacity_arc_count_count]
  by_cases hv : v ∈ Q
  · rw [if_pos hv]
    exact List.nodup_iff_count_eq_one.mp simple v hv
  · rw [if_neg hv]
    exact List.count_eq_zero.mpr hv

/--
---
conclusion: Lax263307.SplitPathProjection.project_simple_path
---
Induct over the split path. An input port has only its paired output port
as a positive-capacity successor. The next input port cannot be the one
just visited, because the path is simple; the connecting arc therefore
represents an original graph edge. Apply induction to the remaining pairs
and preserve both original endpoints and simplicity.

# Attribution

Bonnet–Chang, flow projection in Lemma 7.
-/
theorem project_simple_path {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (large : ℚ≥0) (P : List (Fin (2 * n))) (u v : Fin n)
    (simple : P.Nodup)
    (chain : P.IsChain (fun a b => 0 < (splitInstance G x large).capacity a b))
    (start : P.head? = some (minus u)) (finish : P.getLast? = some (plus v)) :
    ∃ Q : List (Fin n), P = expandRoute Q ∧ Q.Nodup ∧ Q.IsChain G.Adj ∧
      Q.head? = some u ∧ Q.getLast? = some v := by
  cases P with
  | nil => simp at start
  | cons a rest =>
    have ha : a = minus u := by simpa using start
    subst a
    cases rest with
    | nil =>
      have heq : minus u = plus v := by simpa using finish
      exact (minus_ne_plus u v heq).elim
    | cons b tail =>
      have hfirst := (List.isChain_cons_cons.mp chain).1
      rw [capacity_minus] at hfirst
      have hb : b = plus u := by
        by_contra hb
        simp [hb] at hfirst
      subst b
      cases tail with
      | nil =>
        have huv : u = v := plus_injective n (by simpa using finish)
        subst v
        exact ⟨[u], rfl, by simp, by simp, rfl, rfl⟩
      | cons c tail =>
        have hsecond := (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp chain).2).1
        rcases port_cases c with hc | hc
        · let w := original c
          have hcap : 0 < (splitInstance G x large).capacity (plus u) (minus w) := hc ▸ hsecond
          rw [capacity_plus_minus] at hcap
          have hne : u ≠ w := by
            intro huw
            have hnot := (List.nodup_cons.mp simple).1
            apply hnot
            exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
              (Or.inl (hc.trans (congrArg minus huw.symm)).symm)))
          have huw : G.Adj u w := by
            by_contra hadj
            simp [hne, hadj] at hcap
          have htail_simple : (minus w :: tail).Nodup := by
            exact hc ▸ (List.nodup_cons.mp (List.nodup_cons.mp simple).2).2
          have htail_chain : (minus w :: tail).IsChain
              (fun a b => 0 < (splitInstance G x large).capacity a b) := by
            exact hc ▸ (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp chain).2).2
          have htail_finish : (minus w :: tail).getLast? = some (plus v) := by
            have hlast : (c :: tail).getLast? = some (plus v) := by
              simpa only [List.getLast?_cons_cons] using finish
            exact hc ▸ hlast
          obtain ⟨Q, hQ, hnodup, hchain, hhead, hlast⟩ := project_simple_path G x large
            (minus w :: tail) w v htail_simple htail_chain rfl htail_finish
          have huQ : u ∉ Q := by
            intro hu
            have hnot := (List.nodup_cons.mp simple).1
            apply hnot
            right
            rw [hc, hQ]
            exact minus_mem_expand Q u hu
          have hchain' : (u :: Q).IsChain G.Adj := by
            apply List.IsChain.cons hchain
            intro z hz
            have hzw : z = w := by simpa [hhead, eq_comm] using hz
            simpa [hzw] using huw
          refine ⟨u :: Q, ?_, List.nodup_cons.mpr ⟨huQ, hnodup⟩, hchain', rfl, ?_⟩
          · simp only [expandRoute, List.flatMap_cons, List.cons_append, List.nil_append]
            rw [hc, hQ]
            rfl
          · have hnonempty : Q ≠ [] := by intro h; simp [h] at hhead
            simpa only [List.getLast?_cons_of_ne_nil hnonempty] using hlast
        · rw [hc, capacity_plus_plus] at hsecond
          simp at hsecond
termination_by P.length
decreasing_by simp_wf; subst_vars; simp only [List.length_cons]; omega

theorem chain_of_zip {α : Type} (P : List α) (R : α → α → Prop) :
    (∀ p ∈ P.zip P.tail, R p.1 p.2) → P.IsChain R := by
  induction P with
  | nil => intro _; simp
  | cons a P ih =>
    intro h
    cases P with
    | nil => simp
    | cons b P =>
      apply List.isChain_cons_cons.mpr
      refine ⟨h (a, b) (by simp), ?_⟩
      apply ih
      intro p hp
      exact h p (by simpa only [List.tail_cons, List.zip_cons_cons, List.mem_cons] using Or.inr hp)

theorem positive_support_chain {N : ℕ} (network : Network N) (π : VertexWeight N)
    (f : ℝ≥0) (F : PathFlow N) (feasible : IsConcurrentFlow .directed network π f F)
    (P : List (Fin N)) (member : P ∈ F.support) :
    P.IsChain (fun a b => 0 < network.capacity a b) := by
  classical
  apply chain_of_zip
  rintro ⟨a, b⟩ hab
  have hF : 0 < F P := pos_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp member)
  have hc : (0 : ℝ≥0) < (P.zip P.tail).count (a, b) := by
    exact_mod_cast List.count_pos_iff.mpr hab
  have hterm := mul_pos hF hc
  have hsum : F P * ((P.zip P.tail).count (a, b) : ℝ≥0) ≤ arcLoad F a b :=
    Finset.single_le_sum (f := fun Q => F Q * ((Q.zip Q.tail).count (a, b) : ℝ≥0))
      (fun _ _ => bot_le) member
  exact (hterm.trans_le hsum).trans_le (feasible.2.1 a b)

/--
---
conclusion: Lax263307.SplitPathProjection.split_support_projection
---
A positive-flow path uses only positive-capacity arcs: every used arc's
positive contribution is bounded by its total load, hence by its capacity.
The registered flow predicate also supplies path simplicity. Apply the
split-path projection theorem to paths with the retained split endpoints.

# Attribution

Bonnet–Chang, flow projection in Lemma 7.
-/
theorem split_support_projection {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (large : ℚ≥0) (f : ℝ≥0) (F : PathFlow (2 * n))
    (feasible : IsConcurrentFlow .directed (splitInstance G x large).network
      (splitInstance G x large).weights f F)
    (P : List (Fin (2 * n))) (member : P ∈ F.support) (u v : Fin n)
    (start : P.head? = some (minus u)) (finish : P.getLast? = some (plus v)) :
    ∃ Q : List (Fin n), P = expandRoute Q ∧ Q.Nodup ∧ Q.IsChain G.Adj ∧
      Q.head? = some u ∧ Q.getLast? = some v := by
  have hsimple := (feasible.1 P member).2
  have hchain := positive_support_chain (splitInstance G x large).network
    (splitInstance G x large).weights f F feasible P member
  have hchain' : P.IsChain (fun a b => 0 < (splitInstance G x large).capacity a b) := by
    apply hchain.imp
    intro a b h
    change 0 < ((splitInstance G x large).capacity a b : ℝ≥0) at h
    exact_mod_cast h
  exact Lax263307.SplitPathProjection.project_simple_path G x large P u v hsimple hchain' start finish

end Lax263307Proofs.SplitPathProjection
