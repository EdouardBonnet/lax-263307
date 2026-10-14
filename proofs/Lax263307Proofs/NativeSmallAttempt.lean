import Lax263307Proofs.NativeAttemptReply

namespace Lax263307Proofs.NativeSmallAttempt

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307

def Input {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) (σ : Env) : Prop :=
  σ.vars "graph.n"=n ∧ σ.vars "node.k"=k ∧
  Prefix (NativeWeightReduction.adjacency G) "search.graph" σ ∧
  (n+1)*(k+1)≤(σ.arrs "choose.table").length ∧ n≤(σ.arrs "subset.bits").length

def command (ret : ℕ) : Com := .seq (.assign "target.k" (.var "node.k"))
  (.seq NativeExhaustive.command (NativeAttemptReply.command ret))

/-- Execute the exhaustive base case and serialize its exact answer
using the recursive machine's common return protocol. -/
theorem command_spec {n : ℕ} (B ret : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) (hB : n*n+(n+1)*(k+1)+n+k+ret+10<B) (hm : 2^n<B)
    (hcoeff : ∀ i≤n,∀ j≤k,i.choose j<B) :
    Spec B (Input G k) (command ret)
      (fun _ τ => τ.vars "graph.n"=n ∧
        NativeTargetDriver.Reply (ExhaustiveTargets.findIndependentSet G k) τ ∧ τ.vars "machine.phase"=ret)
      (NativeExhaustive.cost n k+15*n+20) := by
  rintro σ ⟨hn,hk,hgraph,htable,hbits⟩
  let ν := σ.setVar "target.k" k
  have r0 : Run B (.assign "target.k" (.var "node.k")) σ ν 2 := Run.assign
    (by rw [evalB_var_iff]; exact ⟨hk.symm,hk ▸ (by omega)⟩)
  obtain ⟨μ,r1,p1⟩ := NativeExhaustive.command_spec B G k (by omega) hcoeff ν
    ⟨(r0.frame_var "graph.n" (by decide)).trans hn,by rfl,
      by simpa only [Prefix,r0.frame_arr "search.graph" (by decide)] using hgraph,
      by rw [RamFrames.run_array_length r0]; exact htable,
      by rw [RamFrames.run_array_length r0]; exact hbits⟩
  have hnμ := ((r0.seq r1).frame_var "graph.n" (by decide)).trans hn
  obtain ⟨τ,r2,p2⟩ := NativeAttemptReply.command_spec B n ret (ExhaustiveTargets.findIndependentSet G k)
    (by omega) hm μ ⟨hnμ,p1⟩
  exact ⟨τ,(r0.seq (r1.seq r2)).mono (by omega),p2⟩

end Lax263307Proofs.NativeSmallAttempt
