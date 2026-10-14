import Lax263307Proofs.NativeTabulate

namespace Lax263307Proofs.NativeBlockAppend

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

def step (source target : String) : Com := .seq
  (RamWordBuffer.append target "stack.words" (.get source (.var "stack.i")))
  (.assign "stack.i" (.add (.var "stack.i") (.lit 1)))

def command (source target : String) : Com := .seq (.assign "stack.i" (.lit 0))
  (.while (.lt (.var "stack.i") (.var "stack.copy.length")) (step source target))

structure Invariant (source target : String) (front xs : List ℕ) (σ : Env) : Prop where
  source : Prefix xs source σ
  count : σ.vars "stack.copy.length"=xs.length
  index : σ.vars "stack.i"≤xs.length
  position : σ.vars "stack.words"=front.length+σ.vars "stack.i"
  room : front.length+xs.length≤(σ.arrs target).length
  target : Prefix (front++xs.take (σ.vars "stack.i")) target σ

theorem step_spec (B : ℕ) (source target : String) (front xs : List ℕ) (hne : source≠target)
    (hB : front.length+xs.length+2<B) (hv : ∀ z∈xs,z<B) :
    Spec B (fun σ => Invariant source target front xs σ ∧ σ.vars "stack.i"<xs.length)
      (step source target) (fun σ τ => Invariant source target front xs τ ∧
        τ.vars "stack.i"=σ.vars "stack.i"+1) 12 := by
  rintro σ ⟨hd,hi⟩
  let i := σ.vars "stack.i"
  have hroom := hd.room
  have hlen : (front++xs.take i).length=front.length+i := by
    rw [List.length_append,List.length_take,Nat.min_eq_left (show i≤xs.length from hd.index)]
  obtain ⟨ν,r1,p1⟩ := RamWordBuffer.append_spec B target "stack.words" (front++xs.take i) xs[i]
    (.get source (.var "stack.i")) (by omega) (by rw [hlen]; omega) σ
    ⟨hd.target,by rw [hlen]; exact hd.position,by rw [hlen]; omega,
      evalB_get (evalB_var (by omega : i<B)) (hd.source i hi) (hv _ (List.getElem_mem hi))⟩
  have hiν : ν.vars "stack.i"=i := r1.frame_var "stack.i" (by simp [RamWordBuffer.append,Com.wvars])
  let τ := ν.setVar "stack.i" (i+1)
  have r2 : Run B (.assign "stack.i" (.add (.var "stack.i") (.lit 1))) ν τ 4 := Run.assign
    (evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hiν.symm,hiν ▸ (by omega : i<B)⟩)
      (evalB_lit (show 1<B by omega)) (by change i+1<B; omega))
  have rr := r1.seq r2
  have ht : τ.vars "stack.i"=i+1 := by simp [τ]
  refine ⟨τ,rr.mono (by simp [Expr.size]),⟨?_,?_,by rw [ht]; omega,?_,?_,?_⟩,ht⟩
  · simpa only [Prefix,rr.frame_arr source (by simp [step,RamWordBuffer.append,Com.warrs,hne])] using hd.source
  · exact (rr.frame_var "stack.copy.length" (by simp [step,RamWordBuffer.append,Com.wvars])).trans hd.count
  · rw [r2.frame_var "stack.words" (by decide),p1.2,hlen,ht]
    omega
  · rw [RamFrames.run_array_length rr]; exact hd.room
  · rw [ht,List.take_succ_eq_append_getElem hi]
    simpa only [Prefix,τ,arrs_setVar,List.append_assoc] using p1.1

/-- Save an initialized buffer at the end of a stack, preserving every
previous frame. Only the initialized source block is read. -/
theorem command_spec (B : ℕ) (source target : String) (front xs : List ℕ) (hne : source≠target)
    (hB : front.length+xs.length+2<B) (hv : ∀ z∈xs,z<B) :
    Spec B (fun σ => Prefix xs source σ ∧ Prefix front target σ ∧
      σ.vars "stack.words"=front.length ∧ σ.vars "stack.copy.length"=xs.length ∧
      front.length+xs.length≤(σ.arrs target).length) (command source target)
      (fun _ τ => Prefix xs source τ ∧ Prefix (front++xs) target τ ∧
        τ.vars "stack.words"=front.length+xs.length) (16*xs.length+6) := by
  have hloop := Spec.forRangeZero "stack.i" "stack.copy.length" (Invariant source target front xs)
    xs.length 12 (by omega) (fun _ h => h.index) (fun _ h => h.count)
    (step_spec B source target front xs hne hB hv)
  rintro σ ⟨hs,hf,hpos,hcount,hroom⟩
  have hi : Invariant source target front xs (σ.setVar "stack.i" 0) := by
    refine ⟨hs,by simpa using hcount,by simp,by simpa using hpos,hroom,?_⟩
    simpa only [Prefix,arrs_setVar,vars_setVar,if_true,List.take_zero,List.append_nil] using hf
  obtain ⟨τ,rr,p⟩ := hloop σ hi
  exact ⟨τ,rr.mono (by nlinarith only []),p.1.source,
    by simpa only [p.2,List.take_length] using p.1.target,by simpa only [p.2] using p.1.position⟩

end Lax263307Proofs.NativeBlockAppend
