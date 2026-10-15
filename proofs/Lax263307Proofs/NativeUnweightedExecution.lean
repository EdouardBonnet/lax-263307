import Lax263307Proofs.NativeSelectedExecution
import Lax263307Proofs.NativeCoreExecution
import Lax263307Proofs.NativeCoreOutput

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeUnweightedExecution

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 GraphClasses
open NativeCoreMachine NativeRootWorkspace

def cost (cfg : Config) (n W : ℕ) : ℕ :=
  let steps := NativeRecursionBudget.work (NativeLocalTime.steps W) (NativeLocalTime.branches W) (RecursionDepth.depth n)
  let time := NativeRecursionBudget.work (NativeLocalTime.time cfg W (stride W)) (NativeLocalTime.branches W) (RecursionDepth.depth n)
  (time+26+68*(steps+3))*n+98

theorem guards (cfg : Config) (n R W w : ℕ) (hn : n ≤ R) (hR : R ≤ W) (hw : hostHeight cfg W ≤ w) :
    stride W*(frameArrays cfg).length+(frameScalars cfg).length+stride W+(frameArrays cfg).length+10<2^w ∧
    n+RecursionDepth.depth n+20<2^w ∧ 2^n<2^w := by
  have hA : (frameArrays cfg).length ≤ stride W*(frameArrays cfg).length := Nat.le_mul_of_pos_left _ (by dsimp only [stride]; omega)
  have hframe : frameLength cfg W ≤ (2*W+2)*frameLength cfg W := Nat.le_mul_of_pos_left _ (by omega)
  have hdep := RecursionDepth.logarithmic_bound n
  have hlog := Nat.log2_le_self n
  have hhost := hw
  dsimp only [hostHeight,NativeNearResources.wordHeight,frameLength,stride] at hhost hA hframe
  have hwidth : n<w := by omega
  refine ⟨?_,?_,Nat.pow_lt_pow_right (by decide) hwidth⟩
  · exact (by dsimp only [stride]; omega :
      stride W*(frameArrays cfg).length+(frameScalars cfg).length+stride W+(frameArrays cfg).length+10 ≤ w).trans_lt Nat.lt_two_pow_self
  · exact (by omega : n+RecursionDepth.depth n+20 ≤ w).trans_lt Nat.lt_two_pow_self

/-- Execute the complete unweighted program with all recursive execution
and solver calls discharged. Its only budget premises are explicit numerical
root bounds with fixed selected programs. -/
theorem command_spec {C : GraphClass} (hereditary : IsHereditary C)
    {lp flow : List ℕ → List ℕ} (p : NativeSelectedLP.Program lp) (q : NativeSelectedNear.Program flow)
    (cfg : Config) (hpc : p.code=cfg.lp) (hpcoeff : p.coeff=cfg.lpWidth)
    (hqc : q.code=cfg.flow) (hqcoeff : q.coeff=cfg.flowWidth)
    (encoded : NativeEncodedLP.Encoded lp) (hsep : NearOracle.SeparatorCorrect C flow cfg.a cfg.K cfg.b)
    (correct : NativeRecursiveOracle.OracleCorrect C lp flow cfg.a cfg.K cfg.b) (hK : 0<cfg.K) (hb : 0<cfg.b)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : G∈C n) (hn : 0<n)
    (D c originalN R W w : ℕ) (hD : 4 ≤ D) (hnR : n ≤ R)
    (program : NativeOracleRounds.Program cfg.rounded c)
    (uniform : ∀ m,0<m → m ≤ n → ParameterResources.resource cfg.a cfg.K cfg.b m D ≤ R)
    (budget : NativeSelectedBudget.demand cfg p q c R ≤ W) (host : hostHeight cfg W ≤ w) :
    Spec (2^w) (NativeCoreExecution.Input (2^w) D (RecursionDepth.depth n) (stride W) W G (extent cfg n W originalN))
      (NativeCoreMachine.command cfg)
      (fun σ τ => NativeCoreExecution.Root (2^w) D (stride W) W cfg G (extent cfg n W originalN) τ ∧
        NativeRootTrace.Answer (RecursiveAlgorithm.solve lp flow cfg.a cfg.K cfg.b D G) τ ∧
        τ.vars "input.n"=σ.vars "input.n" ∧ τ.vars "blowup.length"=σ.vars "blowup.length" ∧
        τ.arrs "blowup.owner"=σ.arrs "blowup.owner" ∧ τ.out=σ.out) (cost cfg n W) := by
  have resources := NativeSelectedExecution.resources hereditary p q cfg hpc hpcoeff hqc hqcoeff encoded hsep correct hK hb
    D c n originalN R W w hD hnR program uniform budget host
  have hdem := budget
  dsimp only [NativeSelectedBudget.demand] at hdem
  have hguards := guards cfg n R W w hnR (by omega) host
  have core := NativeCoreExecution.command_spec D (RecursionDepth.depth n) (stride W) W w
    (NativeLocalTime.steps W) (NativeLocalTime.time cfg W (stride W)) (NativeLocalTime.branches W)
    cfg G lp flow (extent cfg n W originalN) (NativeSelectedExecution.domain C cfg n W) resources
    (fun k hk hkn => NativeRecursiveDomain.root G hG hn (by rfl) k hk hkn)
    hguards.1 hguards.2.1 hguards.2.2
  intro σ hi
  obtain ⟨τ,rr,post⟩ := core σ hi
  exact ⟨τ,rr,post.1,post.2,
    rr.frame_var _ (NativeSourceFrame.command_variable cfg _ (by simp)),
    rr.frame_var _ (NativeSourceFrame.command_variable cfg _ (by simp)),
    rr.frame_arr _ (NativeSourceFrame.command_array cfg _ (by simp)),rr.out_eq (NativeCoreOutput.command cfg)⟩

end Lax263307Proofs.NativeUnweightedExecution
