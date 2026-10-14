import Lax263307Proofs.NativeCutTrace
import Lax263307Proofs.NativeCutTest

set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

namespace Lax263307Proofs.NativeCutLoop

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators NativeMasks

def preserved : List String := ["separator.remaining","separator.value","separator.count","separator.position"]

structure State {n : ℕ} (Q : Env → Prop) (cut : Finset (Fin n) → Finset (Fin n) × Finset (Fin n))
    (start : Finset (Fin n)) (i : ℕ) (σ : Env) (cs : List (Finset (Fin n) × Finset (Fin n))) (R : Finset (Fin n)) : Prop where
  context : Q σ
  length_le : cs.length ≤ i
  suffix : cs++cuts cut (n-i) R=cuts cut n start
  last : R=remaining start cs
  remaining : σ.vars "separator.remaining"=mask R
  separator : σ.vars "separator.value"=mask (ComputedSeparators.separator cs)
  count : σ.vars "separator.count"=cs.length
  prefix_words : Prefix (NativeCutRecords.words cs) "separator.cuts" σ
  position : σ.vars "separator.position"=2*cs.length
  bitroom : n≤(σ.arrs "subset.bits").length
  cutroom : 2*n≤(σ.arrs "separator.cuts").length

def Invariant {n : ℕ} (Q : Env → Prop) (cut : Finset (Fin n) → Finset (Fin n) × Finset (Fin n))
    (start : Finset (Fin n)) (σ : Env) : Prop :=
  σ.vars "separator.i"≤n ∧ ∃ cs R,State Q cut start (σ.vars "separator.i") σ cs R

theorem state_frame {B n i K : ℕ} {Q : Env → Prop}
    {cut : Finset (Fin n) → Finset (Fin n) × Finset (Fin n)} {start R : Finset (Fin n)}
    {cs : List (Finset (Fin n) × Finset (Fin n))} {c : Com} {σ τ : Env}
    (rr : Run B c σ τ K) (hs : State Q cut start i σ cs R) (hq : Q τ)
    (hv : ∀ s∈preserved,s∉c.wvars) (ha : "separator.cuts"∉c.warrs) : State Q cut start i τ cs R := by
  refine ⟨hq,hs.length_le,hs.suffix,hs.last,
    (rr.frame_var "separator.remaining" (hv _ (by simp [preserved]))).trans hs.remaining,
    (rr.frame_var "separator.value" (hv _ (by simp [preserved]))).trans hs.separator,
    (rr.frame_var "separator.count" (hv _ (by simp [preserved]))).trans hs.count,?_,
    (rr.frame_var "separator.position" (hv _ (by simp [preserved]))).trans hs.position,?_,?_⟩
  · simpa only [Prefix,rr.frame_arr "separator.cuts" ha] using hs.prefix_words
  · rw [RamFrames.run_array_length rr]; exact hs.bitroom
  · rw [RamFrames.run_array_length rr]; exact hs.cutroom

def branch (body : Com) : Com := .ite (.eq (.var "separator.active") (.lit 1))
  (.seq body NativeCutRecords.command) .skip

def step (body : Com) : Com := .seq NativeCutTest.command
  (.seq (branch body) (.assign "separator.i" (.add (.var "separator.i") (.lit 1))))

theorem step_spec {n : ℕ} (B K : ℕ) (Q : Env → Prop)
    (cut : Finset (Fin n) → Finset (Fin n) × Finset (Fin n)) (start : Finset (Fin n)) (body : Com)
    (hB : 3*n+5<B) (hm : 2^n<B)
    (horder : ∀ σ,Q σ → σ.vars "graph.n"=n)
    (hset : ∀ σ k,Q σ → Q (σ.setVar "separator.i" k))
    (hcheck : ∀ {σ τ : Env} {k : ℕ},Run B NativeCutTest.command σ τ k → Q σ → Q τ)
    (hrecord : ∀ {σ τ : Env} {k : ℕ},Run B NativeCutRecords.command σ τ k → Q σ → Q τ)
    (hbody : ∀ R : Finset (Fin n),¬3*R.card≤2*n →
      Spec B (fun σ => Q σ ∧ σ.vars "separator.remaining"=mask R) body
        (fun _ τ => Q τ ∧ τ.vars "cut.left"=mask (cut R).1 ∧ τ.vars "cut.right"=mask (cut R).2) K)
    (hvars : ∀ s∈preserved,s∉body.wvars) (hindex : "separator.i"∉body.wvars)
    (harray : "separator.cuts"∉body.warrs) :
    Spec B (fun σ => Invariant Q cut start σ ∧ σ.vars "separator.i"<n) (step body)
      (fun σ τ => Invariant Q cut start τ ∧ τ.vars "separator.i"=σ.vars "separator.i"+1) (21*n+K+58) := by
  rintro σ ⟨⟨hile,cs,R,hs⟩,hlt⟩
  let i := σ.vars "separator.i"
  have hilt : i<n := hlt
  have hlen : cs.length ≤ i := hs.length_le
  have hiB : i<B := by dsimp [i]; omega
  obtain ⟨ν,r1,p1⟩ := NativeCutTest.command_spec B R hB hm σ ⟨horder σ hs.context,hs.remaining,hs.bitroom⟩
  have sn := state_frame r1 hs (hcheck r1 hs.context) (by decide) (by decide)
  have hin : ν.vars "separator.i"=i := r1.frame_var "separator.i" (by decide)
  have hflag : ν.vars "separator.active"<B := by rw [p1.1]; split_ifs <;> omega
  have hc : (Cond.eq (.var "separator.active") (.lit 1)).evalB B ν=
      some (decide ((if 3*R.card≤2*n then 0 else 1)=1)) :=
    evalB_condEq (by rw [evalB_var_iff]; exact ⟨p1.1.symm,hflag⟩) (evalB_lit (by omega))
  have hb : ∃ μ,Run B (branch body) ν μ (K+34) ∧ μ.vars "separator.i"=i ∧
      ∃ cs' R',State Q cut start (i+1) μ cs' R' := by
    by_cases hsmall : 3*R.card≤2*n
    · have rb : Run B (branch body) ν ν (K+34) :=
        (Run.ite_false (c:=.seq body NativeCutRecords.command) (by simpa [hsmall] using hc) Run.skip).mono (by simp [Cond.size,Expr.size] <;> omega)
      refine ⟨ν,rb,hin,cs,R,⟨sn.context,?_,?_,sn.last,sn.remaining,sn.separator,sn.count,sn.prefix_words,sn.position,sn.bitroom,sn.cutroom⟩⟩
      · have hh := sn.length_le; dsimp [i]; omega
      · exact NativeCutTrace.append_stop cut i R hsmall cs (cuts cut n start) sn.suffix
    · obtain ⟨μ,r2,p2⟩ := hbody R hsmall ν ⟨sn.context,sn.remaining⟩
      have sm := state_frame r2 sn p2.1 hvars harray
      obtain ⟨ρ,r3,p3⟩ := NativeCutRecords.command_spec B cs (cut R).1 (cut R).2
        (by omega) hm μ
        ⟨p2.2.1,p2.2.2,sm.separator,sm.count,sm.prefix_words,sm.position,
          by have hh:=sm.cutroom; omega⟩
      have rb : Run B (branch body) ν ρ (K+34) := (Run.ite_true (d:=.skip)
        (by simpa [hsmall] using hc) (r2.seq r3)).mono (by simp [Cond.size,Expr.size] <;> omega)
      have hir : ρ.vars "separator.i"=i :=
        ((r2.seq r3).frame_var "separator.i" (by simp only [Com.wvars,List.mem_append,not_or]; exact ⟨hindex,by decide⟩)).trans hin
      refine ⟨ρ,rb,hir,cs++[cut R],(cut R).1\(cut R).2,
        ⟨hrecord r3 p2.1,?_,?_,?_,p3.1,p3.2.1,?_,p3.2.2.2.1,?_,?_,?_⟩⟩
      · simp only [List.length_append,List.length_singleton]; omega
      · exact NativeCutTrace.append_advance cut i hilt R hsmall cs (cuts cut n start) sm.suffix
      · exact (NativeCutTrace.remaining_snoc start cs (cut R).1 (cut R).2).symm
      · simpa only [List.length_append,List.length_singleton] using p3.2.2.1
      · simpa only [List.length_append,List.length_singleton] using p3.2.2.2.2
      · rw [RamFrames.run_array_length r3]; exact sm.bitroom
      · rw [RamFrames.run_array_length r3]; exact sm.cutroom
  obtain ⟨μ,r2,hiμ,cs',R',sm⟩ := hb
  let τ := μ.setVar "separator.i" (i+1)
  have r3 : Run B (.assign "separator.i" (.add (.var "separator.i") (.lit 1))) μ τ 4 :=
    Run.assign (evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hiμ.symm,hiμ ▸ hiB⟩)
      (evalB_lit (by omega)) (by change i+1<B; dsimp [i]; omega))
  have st := state_frame r3 sm (hset μ (i+1) sm.context) (by decide) (by decide)
  have hit : τ.vars "separator.i"=i+1 := by simp [τ]
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),⟨by rw [hit]; exact hlt,cs',R',by simpa only [hit] using st⟩,hit⟩

def command (body : Com) : Com := .seq (.assign "separator.count" (.lit 0))
  (.seq (.assign "separator.position" (.lit 0)) (.seq (.assign "separator.value" (.lit 0))
    (.seq (.assign "separator.i" (.lit 0)) (.while (.lt (.var "separator.i") (.var "graph.n")) (step body)))))

/-- Execute at most n native cut calls and return the exact functional
cut list, accumulated separator, and final remaining set. The callback
is one fixed command and its execution contract is uniform over R. -/
theorem command_spec {n : ℕ} (B K : ℕ) (Q : Env → Prop)
    (cut : Finset (Fin n) → Finset (Fin n) × Finset (Fin n)) (start : Finset (Fin n)) (body : Com)
    (hB : 3*n+5<B) (hm : 2^n<B)
    (horder : ∀ σ,Q σ → σ.vars "graph.n"=n)
    (hset : ∀ σ s k,s∈["separator.i","separator.count","separator.position","separator.value"] → Q σ → Q (σ.setVar s k))
    (hcheck : ∀ {σ τ : Env} {k : ℕ},Run B NativeCutTest.command σ τ k → Q σ → Q τ)
    (hrecord : ∀ {σ τ : Env} {k : ℕ},Run B NativeCutRecords.command σ τ k → Q σ → Q τ)
    (hbody : ∀ R : Finset (Fin n),¬3*R.card≤2*n →
      Spec B (fun σ => Q σ ∧ σ.vars "separator.remaining"=mask R) body
        (fun _ τ => Q τ ∧ τ.vars "cut.left"=mask (cut R).1 ∧ τ.vars "cut.right"=mask (cut R).2) K)
    (hvars : ∀ s∈preserved,s∉body.wvars) (hindex : "separator.i"∉body.wvars)
    (harray : "separator.cuts"∉body.warrs) :
    Spec B (fun σ => Q σ ∧ σ.vars "separator.remaining"=mask start ∧
      n≤(σ.arrs "subset.bits").length ∧ 2*n≤(σ.arrs "separator.cuts").length) (command body)
      (fun _ τ => Q τ ∧ τ.vars "separator.remaining"=mask (remaining start (cuts cut n start)) ∧
        τ.vars "separator.value"=mask (ComputedSeparators.separator (cuts cut n start)) ∧
        τ.vars "separator.count"=(cuts cut n start).length ∧
        Prefix (NativeCutRecords.words (cuts cut n start)) "separator.cuts" τ ∧
        τ.vars "separator.position"=2*(cuts cut n start).length) ((21*n+K+62)*n+12) := by
  have hstep := step_spec B K Q cut start body hB hm horder
    (fun σ k h => hset σ "separator.i" k (by simp) h) hcheck hrecord hbody hvars hindex harray
  have hloop := Spec.forRangeZero "separator.i" "graph.n" (Invariant Q cut start) n (21*n+K+58)
    (by omega) (fun _ h => h.1)
    (by intro σ h; obtain ⟨cs,R,hs⟩ := h.2; exact horder σ hs.context) hstep
  rintro σ ⟨hq,hR,hbits,hcuts⟩
  let σ1 := σ.setVar "separator.count" 0
  have r1 : Run B (.assign "separator.count" (.lit 0)) σ σ1 2 := Run.assign (evalB_lit (by omega))
  let σ2 := σ1.setVar "separator.position" 0
  have r2 : Run B (.assign "separator.position" (.lit 0)) σ1 σ2 2 := Run.assign (evalB_lit (by omega))
  let σ3 := σ2.setVar "separator.value" 0
  have r3 : Run B (.assign "separator.value" (.lit 0)) σ2 σ3 2 := Run.assign (evalB_lit (by omega))
  have q1 : Q σ1 := hset σ "separator.count" 0 (by simp) hq
  have q2 : Q σ2 := hset σ1 "separator.position" 0 (by simp) q1
  have q3 : Q σ3 := hset σ2 "separator.value" 0 (by simp) q2
  have r0 : Run B (.assign "separator.i" (.lit 0)) σ3 (σ3.setVar "separator.i" 0) 2 :=
    Run.assign (evalB_lit (by omega))
  have rr0 := r1.seq (r2.seq (r3.seq r0))
  have hinit : Invariant Q cut start (σ3.setVar "separator.i" 0) := by
    refine ⟨by simp,[],start,⟨hset σ3 "separator.i" 0 (by simp) q3,by simp,by simp,?_,?_,?_,?_,?_,?_,hbits,hcuts⟩⟩
    · simp [remaining]
    · exact (rr0.frame_var "separator.remaining" (by decide)).trans hR
    · rw [show ComputedSeparators.separator ([] : List (Finset (Fin n) × Finset (Fin n)))=∅ from rfl,mask_empty]
      exact (r0.frame_var "separator.value" (by decide)).trans (by simp only [σ3,vars_setVar,if_true])
    · change (σ3.setVar "separator.i" 0).vars "separator.count"=0
      exact ((r2.seq (r3.seq r0)).frame_var "separator.count" (by decide)).trans
        (by simp only [σ1,vars_setVar,if_true])
    · intro j hj
      change j<0 at hj
      omega
    · change (σ3.setVar "separator.i" 0).vars "separator.position"=0
      exact ((r3.seq r0).frame_var "separator.position" (by decide)).trans
        (by simp only [σ2,vars_setVar,if_true])
  obtain ⟨τ,r4,ht⟩ := hloop σ3 hinit
  obtain ⟨cs,R,hs⟩ := ht.1.2
  rw [ht.2] at hs
  have hcs : cs=cuts cut n start := by simpa only [Nat.sub_self,cuts,List.append_nil] using hs.suffix
  refine ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono (by nlinarith only []),hs.context,?_,?_,?_,?_,?_⟩
  · rw [←hcs,←hs.last]; exact hs.remaining
  · simpa only [←hcs] using hs.separator
  · simpa only [←hcs] using hs.count
  · simpa only [←hcs] using hs.prefix_words
  · simpa only [←hcs] using hs.position

end Lax263307Proofs.NativeCutLoop
