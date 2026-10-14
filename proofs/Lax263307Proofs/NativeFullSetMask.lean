import Lax263307Proofs.NativeMasks

namespace Lax263307Proofs.NativeFullSetMask

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NativeMasks

def Invariant (n : ℕ) (σ : Env) : Prop :=
  σ.vars "graph.n"=n ∧ σ.vars "separator.init.i"≤n ∧
    σ.vars "separator.remaining"=mask (initialSet (Finset.univ : Finset (Fin n)) (σ.vars "separator.init.i"))

def step : Com := .seq (.assign "separator.remaining"
  (.or (.var "separator.remaining") (.shiftl (.lit 1) (.var "separator.init.i"))))
  (.assign "separator.init.i" (.add (.var "separator.init.i") (.lit 1)))

theorem step_spec (B n : ℕ) (hB : n+2<B) (hm : 2^n<B) :
    Spec B (fun σ => Invariant n σ ∧ σ.vars "separator.init.i"<n) step
      (fun σ τ => Invariant n τ ∧ τ.vars "separator.init.i"=σ.vars "separator.init.i"+1) 10 := by
  rintro σ ⟨⟨hn,hle,hmask⟩,hlt⟩
  let i := σ.vars "separator.init.i"
  let U : Finset (Fin n) := Finset.univ
  have hiB : i<B := by dsimp [i]; omega
  have hp : 2^i<B := (Nat.pow_lt_pow_right (by decide : 1<2) hlt).trans hm
  have hprev := (mask_bound (initialSet U i)).trans hm
  have hnext := (mask_bound (initialSet U (i+1))).trans hm
  have hu : Nat.lor (mask (initialSet U i)) (2^i)=mask (initialSet U (i+1)) := by
    simpa only [U,Finset.mem_univ,if_true,one_mul] using prefix_step U i hlt
  have he := evalB_bin (op:=.or)
    (by rw [evalB_var_iff]; exact ⟨hmask.symm,hmask ▸ hprev⟩)
    (evalB_bin (op:=.shiftl) (evalB_lit (show 1<B by omega)) (evalB_var hiB) (by change 1*2^i<B; simpa only [one_mul] using hp))
    (by change Nat.lor (mask (initialSet U i)) (1*2^i)<B; rw [one_mul,hu]; exact hnext)
  have he' : (Expr.or (.var "separator.remaining") (.shiftl (.lit 1) (.var "separator.init.i"))).evalB B σ=
      some (mask (initialSet U (i+1))) := by
    simp only [Bop.apply_or,Bop.apply_shiftl,one_mul] at he
    change (Expr.or (.var "separator.remaining") (.shiftl (.lit 1) (.var "separator.init.i"))).evalB B σ=
      some (Nat.lor (mask (initialSet U i)) (2^i)) at he
    exact he.trans (congrArg some hu)
  let ν := σ.setVar "separator.remaining" (mask (initialSet U (i+1)))
  have r1 : Run B (.assign "separator.remaining"
      (.or (.var "separator.remaining") (.shiftl (.lit 1) (.var "separator.init.i")))) σ ν 6 := Run.assign he'
  have hiν : ν.vars "separator.init.i"=i := r1.frame_var "separator.init.i" (by decide)
  let τ := ν.setVar "separator.init.i" (i+1)
  have r2 : Run B (.assign "separator.init.i" (.add (.var "separator.init.i") (.lit 1))) ν τ 4 :=
    Run.assign (evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hiν.symm,hiν ▸ hiB⟩)
      (evalB_lit (by omega)) (by change i+1<B; dsimp [i]; omega))
  have rr := r1.seq r2
  have hit : τ.vars "separator.init.i"=i+1 := by simp [τ]
  refine ⟨τ,rr,⟨(rr.frame_var "graph.n" (by decide)).trans hn,?_,?_⟩,hit⟩
  · rw [hit]; exact hlt
  · rw [hit]
    exact (r2.frame_var "separator.remaining" (by decide)).trans (by simp only [ν,vars_setVar,if_true] <;> rfl)

def command : Com := .seq (.assign "separator.remaining" (.lit 0))
  (.seq (.assign "separator.init.i" (.lit 0)) (.while (.lt (.var "separator.init.i") (.var "graph.n")) step))

/-- Initialize the remaining set to all vertices directly from the
graph order. No subset word or vertex list is supplied as advice. -/
theorem command_spec (B n : ℕ) (hB : n+2<B) (hm : 2^n<B) :
    Spec B (fun σ => σ.vars "graph.n"=n) command
      (fun _ τ => τ.vars "separator.remaining"=mask (Finset.univ : Finset (Fin n))) (14*n+8) := by
  have hloop := Spec.forRangeZero "separator.init.i" "graph.n" (Invariant n) n 10 (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1) (step_spec B n hB hm)
  intro σ hn
  let ν := σ.setVar "separator.remaining" 0
  have r1 : Run B (.assign "separator.remaining" (.lit 0)) σ ν 2 := Run.assign (evalB_lit (by omega))
  have r0 : Run B (.assign "separator.init.i" (.lit 0)) ν (ν.setVar "separator.init.i" 0) 2 :=
    Run.assign (evalB_lit (by omega))
  have hinit : Invariant n (ν.setVar "separator.init.i" 0) := by
    refine ⟨?_,by simp,?_⟩
    · exact ((r1.seq r0).frame_var "graph.n" (by decide)).trans hn
    · change (ν.setVar "separator.init.i" 0).vars "separator.remaining"=mask (initialSet (Finset.univ : Finset (Fin n)) 0)
      rw [prefix_zero,mask_empty]
      exact (r0.frame_var "separator.remaining" (by decide)).trans (by simp only [ν,vars_setVar,if_true] <;> rfl)
  obtain ⟨τ,r2,ht⟩ := hloop ν hinit
  exact ⟨τ,(r1.seq r2).mono (by omega),by simpa only [ht.2,prefix_full] using ht.1.2.2⟩

end Lax263307Proofs.NativeFullSetMask
