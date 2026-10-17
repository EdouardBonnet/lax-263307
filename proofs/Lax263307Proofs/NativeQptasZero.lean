import Lax263307.IndependentSetEncoding
import Lax263307Proofs.NativeQptasProgram

namespace Lax263307Proofs.NativeQptasZero

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax263307 WeightedIndependentSet NativeFrontend

/-- The complete weighted program's zero-copy branch, including reading
and reducing the original input and emitting all original membership bits. -/
theorem command_spec {n : ℕ} (B M : ℕ) (hM : 1≤M) (hn : n≤M)
    (cfg : NativeCoreMachine.Config) (C d Q e : ℕ) (lp flow : List ℕ → List ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (weights : Fin n → ℚ) (ε : ℚ)
    (hεpos : 0<ε) (hw : ∀ v,(weights v).num.natAbs≤M ∧ (weights v).den≤M)
    (hε : ε.num.natAbs≤M ∧ ε.den≤M) (hB : 2*M^4+3<B) (hsize : n*n+3*n+3<B)
    (hzero : (∑ v,WeightRounding.copies (PositiveWeights.positiveWeights weights) ε v)=0) :
    Spec B (fun σ => σ.inp=encodeInput G weights ε ∧ n*n+3*n+3≤(σ.arrs "input.data").length ∧
      n≤(σ.arrs "copy.counts").length ∧ (σ.arrs "weighted.output").length=n)
      (NativeQptasProgram.command cfg C d Q e)
      (fun σ τ => τ.out=σ.out++encodeOutput (WeightedAlgorithm.solve lp flow cfg.a cfg.K cfg.b G weights ε))
      (NativeBlowUp.cost n 0+24*n+20) := by
  have hz : (∑ v,WeightRounding.copies (fun v => max (weights v) 0) ε v)=0 := hzero
  rintro σ ⟨hinp,hinput,hcounts,houtput⟩
  obtain ⟨ν,r1,hmatrix,howner,hN,hdata,hout,horder⟩ := NativeBlowUp.prepare_spec B M hM hn G weights ε
    hεpos hw hε hB hsize (by rw [hz]; simp; omega) σ
    ⟨hinp,hinput,hcounts,by rw [hz]; omega,by rw [hz]; simp⟩
  have hN0 : ν.vars "blowup.length"=0 := hN.trans hz
  let μ := ν.setVar "graph.n" 0
  have r2 : Run B NativeQptasProgram.order ν μ 2 := Run.assign (by
    rw [evalB_var_iff]; exact ⟨hN0.symm,hN0 ▸ (by omega)⟩)
  have hnμ : μ.vars "input.n"=n := (r2.frame_var _ (by decide)).trans horder
  obtain ⟨τ,r3,post⟩ := NativeEmptyOutput.command_spec B n (by omega) μ
    ⟨hnμ,by rw [RamFrames.run_array_length (r1.seq r2)]; exact houtput⟩
  have htest : (Cond.eq (.var "graph.n") (.lit 0)).evalB B μ=some true :=
    evalB_condEq (show (Expr.var "graph.n").evalB B μ=some 0 from by
      rw [evalB_var_iff]; simp [μ]; omega) (evalB_lit (by omega : 0<B))
  have run : Run B (NativeQptasProgram.command cfg C d Q e) σ τ _ :=
    r1.seq (r2.seq (Run.ite_true htest r3))
  refine ⟨τ,run.mono (by rw [hz]; simp [Cond.size,Expr.size]; omega),?_⟩
  rw [NativeQptasProgram.zero_size_result lp flow cfg.a cfg.K cfg.b G weights ε hzero]
  change τ.out=σ.out++encodeOutput (∅ : Finset (Fin n))
  rw [post,(r2.out_eq (by decide)).trans hout]

end Lax263307Proofs.NativeQptasZero
