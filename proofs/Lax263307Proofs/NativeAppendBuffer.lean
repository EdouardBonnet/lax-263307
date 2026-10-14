import Lax263307Proofs.NativeTabulate

namespace Lax263307Proofs.NativeAppendBuffer

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

def Names (index cursor count : String) : Prop := index≠cursor ∧ index≠count ∧ cursor≠count

def step (source target index cursor : String) : Com := .seq
  (RamWordBuffer.append target cursor (.get source (.var index)))
  (.assign index (.add (.var index) (.lit 1)))

def command (source target index cursor count : String) : Com := .seq (.assign index (.lit 0))
  (.while (.lt (.var index) (.var count)) (step source target index cursor))

structure Invariant (source target index cursor count : String) (front xs : List ℕ) (σ : Env) : Prop where
  source : Prefix xs source σ
  count : σ.vars count=xs.length
  counter : σ.vars index≤xs.length
  position : σ.vars cursor=front.length+σ.vars index
  room : front.length+xs.length≤(σ.arrs target).length
  target : Prefix (front++xs.take (σ.vars index)) target σ

theorem step_spec (B : ℕ) (source target index cursor count : String) (front xs : List ℕ)
    (hnames : Names index cursor count) (hne : source≠target)
    (hB : front.length+xs.length+2<B) (hv : ∀ z∈xs,z<B) :
    Spec B (fun σ => Invariant source target index cursor count front xs σ ∧ σ.vars index<xs.length)
      (step source target index cursor) (fun σ τ => Invariant source target index cursor count front xs τ ∧
        τ.vars index=σ.vars index+1) 12 := by
  rintro σ ⟨hd,hi⟩
  let i := σ.vars index
  have hroom := hd.room
  have hlen : (front++xs.take i).length=front.length+i := by
    rw [List.length_append,List.length_take,Nat.min_eq_left (show i≤xs.length from hd.counter)]
  obtain ⟨ν,r1,p1⟩ := RamWordBuffer.append_spec B target cursor (front++xs.take i) xs[i]
    (.get source (.var index)) (by omega) (by rw [hlen]; omega) σ
    ⟨hd.target,by rw [hlen]; exact hd.position,by rw [hlen]; omega,
      evalB_get (evalB_var (by omega : i<B)) (hd.source i hi) (hv _ (List.getElem_mem hi))⟩
  have hiν : ν.vars index=i := r1.frame_var index (by simp [RamWordBuffer.append,Com.wvars,hnames.1])
  let τ := ν.setVar index (i+1)
  have r2 : Run B (.assign index (.add (.var index) (.lit 1))) ν τ 4 := Run.assign
    (evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hiν.symm,hiν ▸ (by omega : i<B)⟩)
      (evalB_lit (show 1<B by omega)) (by change i+1<B; omega))
  have rr := r1.seq r2
  have ht : τ.vars index=i+1 := by simp [τ]
  refine ⟨τ,rr.mono (by simp [Expr.size]),⟨?_,?_,by rw [ht]; omega,?_,?_,?_⟩,ht⟩
  · simpa only [Prefix,rr.frame_arr source (by simp [step,RamWordBuffer.append,Com.warrs,hne])] using hd.source
  · exact (rr.frame_var count (by simp [step,RamWordBuffer.append,Com.wvars,Ne.symm hnames.2.1,Ne.symm hnames.2.2])).trans hd.count
  · rw [r2.frame_var cursor (by simp [Com.wvars,Ne.symm hnames.1]),p1.2,hlen,ht]
    omega
  · rw [RamFrames.run_array_length rr]; exact hd.room
  · rw [ht,List.take_succ_eq_append_getElem hi]
    simpa only [Prefix,τ,arrs_setVar,List.append_assoc] using p1.1

/-- Append a buffered word block with independently named control
variables, so query construction cannot overwrite recursion-stack cursors. -/
theorem command_spec (B : ℕ) (source target index cursor count : String) (front xs : List ℕ)
    (hnames : Names index cursor count) (hne : source≠target)
    (hB : front.length+xs.length+2<B) (hv : ∀ z∈xs,z<B) :
    Spec B (fun σ => Prefix xs source σ ∧ Prefix front target σ ∧
      σ.vars cursor=front.length ∧ σ.vars count=xs.length ∧
      front.length+xs.length≤(σ.arrs target).length) (command source target index cursor count)
      (fun _ τ => Prefix xs source τ ∧ Prefix (front++xs) target τ ∧
        τ.vars cursor=front.length+xs.length) (16*xs.length+6) := by
  have hloop := Spec.forRangeZero index count (Invariant source target index cursor count front xs)
    xs.length 12 (by omega) (fun _ h => h.counter) (fun _ h => h.count)
    (step_spec B source target index cursor count front xs hnames hne hB hv)
  rintro σ ⟨hs,hf,hpos,hcount,hroom⟩
  have hi : Invariant source target index cursor count front xs (σ.setVar index 0) := by
    refine ⟨hs,by simpa [Ne.symm hnames.2.1] using hcount,by simp,?_,hroom,?_⟩
    · simpa [Ne.symm hnames.1] using hpos
    · simpa only [Prefix,arrs_setVar,vars_setVar,if_true,List.take_zero,List.append_nil] using hf
  obtain ⟨τ,rr,p⟩ := hloop σ hi
  exact ⟨τ,rr.mono (by nlinarith only []),p.1.source,
    by simpa only [p.2,List.take_length] using p.1.target,by simpa only [p.2] using p.1.position⟩

end Lax263307Proofs.NativeAppendBuffer
