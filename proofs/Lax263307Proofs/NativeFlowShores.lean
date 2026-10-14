import Lax263307Proofs.NativeShoreUpdate

set_option maxRecDepth 20000
set_option maxHeartbeats 800000

namespace Lax263307Proofs.NativeFlowShores

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators VertexSplitting
open NativeShoreMasks NativeShoreUpdate

def Context {n : ℕ} (R : Finset (Fin n)) (xs : List ℕ) (σ : Env) : Prop :=
  Prefix (NativeRestrictionOrder.words R) "restrict.vertices" σ ∧ σ.vars "restrict.count"=R.card ∧
    Prefix xs "vm.output" σ ∧ σ.vars "vm.outputLength"=xs.length

theorem frame {B n K : ℕ} {R : Finset (Fin n)} {xs : List ℕ} {c : Com} {σ τ : Env}
    (rr : Run B c σ τ K) (hd : Context R xs σ)
    (ha : ∀ s∈["restrict.vertices","vm.output"],s∉c.warrs)
    (hv : ∀ s∈["restrict.count","vm.outputLength"],s∉c.wvars) : Context R xs τ := by
  refine ⟨?_,(rr.frame_var _ (hv _ (by simp))).trans hd.2.1,?_,(rr.frame_var _ (hv _ (by simp))).trans hd.2.2.2⟩
  · simpa only [Prefix,rr.frame_arr "restrict.vertices" (ha _ (by simp))] using hd.1
  · simpa only [Prefix,rr.frame_arr "vm.output" (ha _ (by simp))] using hd.2.2.1

def left {n : ℕ} (R : Finset (Fin n)) (xs : List ℕ) : Finset (Fin R.card) := leftShore (decodeCut (2*R.card) xs)
def right {n : ℕ} (R : Finset (Fin n)) (xs : List ℕ) : Finset (Fin R.card) := rightShore (decodeCut (2*R.card) xs)

def Invariant {n : ℕ} (R : Finset (Fin n)) (xs : List ℕ) (σ : Env) : Prop :=
  Context R xs σ ∧ σ.vars "shore.i"≤R.card ∧
    σ.vars "shore.left"=partialMask (label R) (left R xs) (σ.vars "shore.i") ∧
    σ.vars "shore.right"=partialMask (label R) (right R xs) (σ.vars "shore.i")

def leftIndex : Com := .assign "output.index" (.mul (.lit 2) (.var "shore.i"))
def rightIndex : Com := .assign "output.index" (.add (.mul (.lit 2) (.var "shore.i")) (.lit 1))
def next : Com := .assign "shore.i" (.add (.var "shore.i") (.lit 1))

def step : Com := .seq (.assign "shore.label" (.get "restrict.vertices" (.var "shore.i")))
  (.seq leftIndex (.seq (bitCommand false) (.seq (maskCommand "shore.left")
    (.seq rightIndex (.seq (bitCommand true) (.seq (maskCommand "shore.right") next))))))

theorem step_spec (B n : ℕ) (R : Finset (Fin n)) (xs : List ℕ)
    (hB : xs.length+2*n+4<B) (hm : 2^n<B) (hw : ∀ x∈xs,x<B) :
    Spec B (fun σ => Invariant R xs σ ∧ σ.vars "shore.i"<R.card) step
      (fun σ τ => Invariant R xs τ ∧ τ.vars "shore.i"=σ.vars "shore.i"+1) 55 := by
  have hR := NativeMaskUnpack.card_bound R
  rintro σ ⟨⟨hc,hle,hleft,hright⟩,hlt⟩
  let i : Fin R.card := ⟨σ.vars "shore.i",hlt⟩
  let v := label R i
  have hiB : i.val<B := by dsimp [i]; omega
  have hvB : v.val<B := v.isLt.trans (by omega)
  have hg : (σ.arrs "restrict.vertices")[i.val]?=some v.val := by
    simpa only [NativeRestrictionOrder.words,List.getElem_ofFn] using
      hc.1 i.val (by simpa only [NativeRestrictionOrder.words,List.length_ofFn] using i.isLt)
  let σ1 := σ.setVar "shore.label" v.val
  have r1 : Run B (.assign "shore.label" (.get "restrict.vertices" (.var "shore.i"))) σ σ1 3 :=
    Run.assign (evalB_get (evalB_var hiB) hg hvB)
  let σ2 := σ1.setVar "output.index" (2*i.val)
  have r2 : Run B leftIndex σ1 σ2 4 := Run.assign
    (evalB_bin (op:=.mul) (evalB_lit (by omega))
      (by rw [evalB_var_iff]; simp only [σ1,vars_setVar,String.reduceEq,if_false]; exact ⟨rfl,hiB⟩)
      (by change 2*i.val<B; have hh:=i.isLt; omega))
  have d2 := frame (r1.seq r2) hc (by decide) (by decide)
  obtain ⟨σ3,r3,p3⟩ := bit_spec B xs (2*i.val) false (by have hh:=i.isLt; omega) hw σ2
    ⟨d2.2.2.1,d2.2.2.2,by simp [σ2]⟩
  have r123 := r1.seq (r2.seq r3)
  obtain ⟨σ4,r4,p4⟩ := mask_spec B "shore.left" (label R) (left R xs) i (by omega) hm σ3
    ⟨(r123.frame_var "shore.left" (by decide)).trans hleft,
      by simpa only [Bool.false_eq_true,if_false,left,left_member] using p3,
      by simpa only [σ1,vars_setVar,if_true] using (r2.seq r3).frame_var "shore.label" (by decide)⟩
  have r1234 := r1.seq (r2.seq (r3.seq r4))
  have hi4 : σ4.vars "shore.i"=i.val := r1234.frame_var "shore.i" (by decide)
  let σ5 := σ4.setVar "output.index" (2*i.val+1)
  have r5 : Run B rightIndex σ4 σ5 6 := Run.assign
    (evalB_bin (op:=.add) (evalB_bin (op:=.mul) (evalB_lit (by omega))
      (by rw [evalB_var_iff]; exact ⟨hi4.symm,hi4 ▸ hiB⟩)
      (by change 2*i.val<B; have hh:=i.isLt; omega)) (evalB_lit (by omega))
      (by change 2*i.val+1<B; have hh:=i.isLt; omega))
  have d5 := frame (r1234.seq r5) hc (by decide) (by decide)
  obtain ⟨σ6,r6,p6⟩ := bit_spec B xs (2*i.val+1) true (by have hh:=i.isLt; omega) hw σ5
    ⟨d5.2.2.1,d5.2.2.2,by simp [σ5]⟩
  have r123456 := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6))))
  obtain ⟨σ7,r7,p7⟩ := mask_spec B "shore.right" (label R) (right R xs) i (by omega) hm σ6
    ⟨(r123456.frame_var "shore.right" (by decide)).trans hright,
      by simpa only [if_true,right,right_member] using p6,
      by simpa only [σ1,vars_setVar,if_true] using (r2.seq (r3.seq (r4.seq (r5.seq r6)))).frame_var "shore.label" (by decide)⟩
  have r1234567 := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))
  have hi7 : σ7.vars "shore.i"=i.val := r1234567.frame_var "shore.i" (by decide)
  let τ := σ7.setVar "shore.i" (i.val+1)
  have r8 : Run B next σ7 τ 4 := Run.assign
    (evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hi7.symm,hi7 ▸ hiB⟩)
      (evalB_lit (by omega)) (by change i.val+1<B; have hh:=i.isLt; omega))
  have rr := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq r8))))))
  have hit : τ.vars "shore.i"=i.val+1 := by simp [τ]
  refine ⟨τ,rr,⟨frame rr hc (by decide) (by decide),?_,?_,?_⟩,hit⟩
  · rw [hit]; exact i.isLt
  · rw [hit]
    exact ((r5.seq (r6.seq (r7.seq r8))).frame_var "shore.left" (by decide)).trans p4
  · rw [hit]
    exact (r8.frame_var "shore.right" (by decide)).trans p7

def command : Com := .seq (.assign "shore.left" (.lit 0)) (.seq (.assign "shore.right" (.lit 0))
  (.seq (.assign "shore.i" (.lit 0)) (.while (.lt (.var "shore.i") (.var "restrict.count")) step)))

/-- Decode the two split-cut shores and lift their vertices through the
actual induced-graph labels, without assuming anything about the output. -/
theorem command_spec (B n : ℕ) (R : Finset (Fin n)) (xs : List ℕ)
    (hB : xs.length+2*n+4<B) (hm : 2^n<B) (hw : ∀ x∈xs,x<B) :
    Spec B (Context R xs) command
      (fun _ τ => Context R xs τ ∧
        τ.vars "shore.left"=NativeMasks.mask ((left R xs).image (label R)) ∧
        τ.vars "shore.right"=NativeMasks.mask ((right R xs).image (label R))) (59*R.card+10) := by
  have hR := NativeMaskUnpack.card_bound R
  have hloop := Spec.forRangeZero "shore.i" "restrict.count" (Invariant R xs) R.card 55 (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1.2.1) (step_spec B n R xs hB hm hw)
  intro σ hc
  let ν := σ.setVar "shore.left" 0
  have r1 : Run B (.assign "shore.left" (.lit 0)) σ ν 2 := Run.assign (evalB_lit (by omega))
  let μ := ν.setVar "shore.right" 0
  have r2 : Run B (.assign "shore.right" (.lit 0)) ν μ 2 := Run.assign (evalB_lit (by omega))
  have hinit : Invariant R xs (μ.setVar "shore.i" 0) := by
    refine ⟨?_,by simp,?_,?_⟩
    · simpa only [Context,Prefix,μ,ν,vars_setVar,arrs_setVar,String.reduceEq,if_false] using hc
    · simp [μ,ν,zero]
    · simp [μ,ν,zero]
  obtain ⟨τ,r3,ht⟩ := hloop μ hinit
  refine ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),ht.1.1,?_,?_⟩
  · simpa only [ht.2,full] using ht.1.2.2.1
  · simpa only [ht.2,full] using ht.1.2.2.2

end Lax263307Proofs.NativeFlowShores
