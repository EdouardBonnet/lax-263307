import Lax263307Proofs.NativeRestrictionOrder
import Lax263307Proofs.NativeMaskUnpack

namespace Lax263307Proofs.NativeChildLift

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators NativeMasks

def selected {n : ℕ} (R : Finset (Fin n)) (I : Finset (Fin R.card)) (i : ℕ) : Finset (Fin n) :=
  (initialSet I i).image (label R)

theorem selected_step {n : ℕ} (R : Finset (Fin n)) (I : Finset (Fin R.card))
    (i : ℕ) (hi : i<R.card) :
    selected R I (i+1)=if (⟨i,hi⟩ : Fin R.card)∈I then
      insert (label R ⟨i,hi⟩) (selected R I i) else selected R I i := by
  rw [selected,prefix_succ I i hi]
  split_ifs <;> simp only [Finset.image_insert,selected]

structure Context {n : ℕ} (R : Finset (Fin n)) (I : Finset (Fin R.card)) (σ : Env) : Prop where
  order : σ.vars "graph.n"=R.card
  bits : Prefix (WeightedIndependentSet.encodeOutput I) "subset.bits" σ
  labels : Prefix (NativeRestrictionOrder.words R) "restrict.vertices" σ

theorem frame {B K n : ℕ} {R : Finset (Fin n)} {I : Finset (Fin R.card)} {c : Com} {σ τ : Env}
    (rr : Run B c σ τ K) (hd : Context R I σ) (hn : "graph.n"∉c.wvars)
    (hb : "subset.bits"∉c.warrs) (hl : "restrict.vertices"∉c.warrs) : Context R I τ := by
  refine ⟨(rr.frame_var _ hn).trans hd.order,?_,?_⟩
  · simpa only [Prefix,rr.frame_arr "subset.bits" hb] using hd.bits
  · simpa only [Prefix,rr.frame_arr "restrict.vertices" hl] using hd.labels

structure Invariant {n : ℕ} (R : Finset (Fin n)) (I : Finset (Fin R.card)) (σ : Env) : Prop where
  context : Context R I σ
  index : σ.vars "lift.i"≤R.card
  value : σ.vars "lift.mask"=mask (selected R I (σ.vars "lift.i"))

def insertCommand : Com := .assign "lift.mask"
  (.or (.var "lift.mask") (.shiftl (.lit 1) (.var "lift.vertex")))

def choose : Com := .ite (.eq (.var "lift.bit") (.lit 1)) insertCommand .skip

def step : Com := .seq (.assign "lift.bit" (.get "subset.bits" (.var "lift.i")))
  (.seq (.assign "lift.vertex" (.get "restrict.vertices" (.var "lift.i")))
    (.seq choose (.assign "lift.i" (.add (.var "lift.i") (.lit 1)))))

theorem step_spec (B n : ℕ) (R : Finset (Fin n)) (I : Finset (Fin R.card))
    (hB : n+2<B) (hm : 2^n<B) :
    Spec B (fun σ => Invariant R I σ ∧ σ.vars "lift.i"<R.card) step
      (fun σ τ => Invariant R I τ ∧ τ.vars "lift.i"=σ.vars "lift.i"+1) 20 := by
  rintro σ ⟨hd,hi⟩
  let i := σ.vars "lift.i"
  let v := label R (⟨i,hi⟩ : Fin R.card)
  let bit : ℕ := if (⟨i,hi⟩ : Fin R.card)∈I then 1 else 0
  have hr := NativeMaskUnpack.card_bound R
  have hiB : i<B := hi.trans_le hr |>.trans (by omega)
  have hvB : v.val<B := v.isLt.trans (by omega)
  have hbB : bit<B := by dsimp [bit]; split_ifs <;> omega
  have hgetb : (σ.arrs "subset.bits")[i]?=some bit := by
    simpa only [WeightedIndependentSet.encodeOutput,List.getElem_ofFn] using
      hd.context.bits i (by simpa only [WeightedIndependentSet.encodeOutput,List.length_ofFn] using hi)
  have hgetv : (σ.arrs "restrict.vertices")[i]?=some v.val := by
    simpa only [NativeRestrictionOrder.words,List.getElem_ofFn] using
      hd.context.labels i (by simpa only [NativeRestrictionOrder.words,List.length_ofFn] using hi)
  let ν := σ.setVar "lift.bit" bit
  have r1 : Run B (.assign "lift.bit" (.get "subset.bits" (.var "lift.i"))) σ ν 3 := Run.assign
    (evalB_get (evalB_var hiB) hgetb hbB)
  let μ := ν.setVar "lift.vertex" v.val
  have r2 : Run B (.assign "lift.vertex" (.get "restrict.vertices" (.var "lift.i"))) ν μ 3 := Run.assign
    (evalB_get (by rw [evalB_var_iff]; exact ⟨(r1.frame_var "lift.i" (by decide)).symm,
      (r1.frame_var "lift.i" (by decide)) ▸ hiB⟩) hgetv hvB)
  have hc : (Cond.eq (.var "lift.bit") (.lit 1)).evalB B μ=some (decide (bit=1)) :=
    evalB_condEq (by rw [evalB_var_iff]; simp [μ,ν,hbB]) (evalB_lit (show 1<B by omega))
  have hmμ : μ.vars "lift.mask"=mask (selected R I i) :=
    ((r1.seq r2).frame_var "lift.mask" (by decide)).trans hd.value
  have hbranch : ∃ ρ,Run B choose μ ρ 10 ∧ ρ.vars "lift.mask"=mask (selected R I (i+1)) := by
    by_cases h : (⟨i,hi⟩ : Fin R.card)∈I
    · have hnew : Nat.lor (mask (selected R I i)) (2^v.val)=mask (selected R I (i+1)) := by
        rw [selected_step R I i hi,if_pos h]
        exact (mask_insert _ v).symm
      let ρ := μ.setVar "lift.mask" (mask (selected R I (i+1)))
      have he : (Expr.or (.var "lift.mask") (.shiftl (.lit 1) (.var "lift.vertex"))).evalB B μ=
          some (mask (selected R I (i+1))) := by
        have hh : (Expr.or (.var "lift.mask") (.shiftl (.lit 1) (.var "lift.vertex"))).evalB B μ=
            some (Nat.lor (mask (selected R I i)) (1*2^v.val)) := evalB_bin (op:=.or)
          (by rw [evalB_var_iff]; exact ⟨hmμ.symm,hmμ ▸ (mask_bound _).trans hm⟩)
          (evalB_bin (op:=.shiftl) (evalB_lit (show 1<B by omega))
            (by rw [evalB_var_iff]; simp [μ,hvB])
            (by change 1*2^v.val<B; rw [one_mul]; exact (Nat.pow_le_pow_right (by decide) v.isLt.le).trans_lt hm))
          (by change Nat.lor (mask (selected R I i)) (1*2^v.val)<B; rw [one_mul,hnew]; exact (mask_bound _).trans hm)
        simpa only [Bop.apply_or,Bop.apply_shiftl,one_mul,hnew] using hh
      have rr : Run B insertCommand μ ρ 6 := Run.assign he
      exact ⟨ρ,(Run.ite_true (d:=.skip) (by simpa [bit,h] using hc) rr).mono (by decide),by simp [ρ]⟩
    · exact ⟨μ,(Run.ite_false (c:=insertCommand) (by simpa [bit,h] using hc) Run.skip).mono (by decide),
        by rw [selected_step R I i hi,if_neg h]; exact hmμ⟩
  obtain ⟨ρ,r3,hmask⟩ := hbranch
  have rr := r1.seq (r2.seq r3)
  have hiρ : ρ.vars "lift.i"=i := rr.frame_var "lift.i" (by decide)
  let τ := ρ.setVar "lift.i" (i+1)
  have r4 : Run B (.assign "lift.i" (.add (.var "lift.i") (.lit 1))) ρ τ 4 := Run.assign
    (evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hiρ.symm,hiρ ▸ hiB⟩)
      (evalB_lit (show 1<B by omega)) (by change i+1<B; omega))
  have ht : τ.vars "lift.i"=i+1 := by simp [τ]
  exact ⟨τ,r1.seq (r2.seq (r3.seq r4)),
    ⟨frame (rr.seq r4) hd.context (by decide) (by decide) (by decide),by rw [ht]; omega,
      by rw [ht]; exact (r4.frame_var "lift.mask" (by decide)).trans hmask⟩,ht⟩

def command : Com := .seq (.assign "lift.mask" (.lit 0))
  (.seq (.assign "lift.i" (.lit 0)) (.while (.lt (.var "lift.i") (.var "graph.n")) step))

/-- Lift a child's selected-set bits through the saved canonical labels
to an exact parent-vertex mask, without inspecting any other vertices. -/
theorem command_spec (B n : ℕ) (R : Finset (Fin n)) (I : Finset (Fin R.card))
    (hB : n+2<B) (hm : 2^n<B) :
    Spec B (Context R I) command
      (fun _ τ => Context R I τ ∧ τ.vars "lift.mask"=mask (I.image (label R))) (24*R.card+8) := by
  have hr := NativeMaskUnpack.card_bound R
  have hloop := Spec.forRangeZero "lift.i" "graph.n" (Invariant R I) R.card 20 (by omega)
    (fun _ h => h.index) (fun _ h => h.context.order) (step_spec B n R I hB hm)
  intro σ hd
  let ν := σ.setVar "lift.mask" 0
  have r1 : Run B (.assign "lift.mask" (.lit 0)) σ ν 2 := Run.assign (evalB_lit (show 0<B by omega))
  have r0 : Run B (.assign "lift.i" (.lit 0)) ν (ν.setVar "lift.i" 0) 2 := Run.assign (evalB_lit (show 0<B by omega))
  have hi : Invariant R I (ν.setVar "lift.i" 0) := by
    refine ⟨frame (r1.seq r0) hd (by decide) (by decide) (by decide),by simp,?_⟩
    simp only [vars_setVar,if_true,selected,prefix_zero,Finset.image_empty,mask_empty]
    exact (r0.frame_var "lift.mask" (by decide)).trans (by simp [ν])
  obtain ⟨τ,r2,p2⟩ := hloop ν hi
  exact ⟨τ,(r1.seq r2).mono (by omega),p2.1.context,
    by simpa only [p2.2,selected,prefix_full] using p2.1.value⟩

end Lax263307Proofs.NativeChildLift
