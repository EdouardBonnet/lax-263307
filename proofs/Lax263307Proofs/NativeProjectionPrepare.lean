import Lax263307Proofs.NativeProjectionCenter
import Lax263307Proofs.NativeNodeTolerance
import Lax263307Proofs.NativeArrayBounds

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeProjectionPrepare

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.LinearProgram Lax109476.RationalEncoding NativeSignedArithmetic

def command : Com := .seq NativeProgramCache.restore
  (.seq NativeProjectionCenter.command NativeNodeTolerance.command)

/-- Prepare a projection call from persistent node data: restore its
base LP, scale its current center, and compute its exact tolerance. -/
theorem command_spec (B M n D R m N : ℕ) (P : Program ℚ m N) (x : Fin N → ℚ)
    (hn : 0<n) (hD : 0<D) (hR : 0<R)
    (hLP : (encodeProgram P).length+2<B) (hB : 2*M^2+3<B)
    (hshape : 4*N+5<B) (hscale : 4*N≤M) (hx : ∀ j,Bounded M (x j))
    (htol : NativeNodeTolerance.guard n D R<B) :
    Spec B (fun σ => NativeProjectionCenter.Context x σ ∧ NativeNodeTolerance.Context n D R σ ∧
      Prefix (encodeProgram P) "moment.program" σ ∧ σ.vars "node.programLength"=(encodeProgram P).length ∧
      NativeArrayBounds.Bounded B σ ∧ (encodeProgram P).length≤(σ.arrs "lp.input").length ∧
      3*N<(σ.arrs "lp.word").length ∧ 3*N≤(σ.arrs "projection.center").length ∧
      3≤(σ.arrs "lp.word").length ∧ 3≤(σ.arrs "projection.tolerance").length) command
      (fun _ τ => NativeProjectionCenter.Context x τ ∧ NativeNodeTolerance.Context n D R τ ∧
        Prefix (encodeProgram P) "lp.input" τ ∧
        Prefix (encodeVector (Lax263307.ProjectedOracle.raw x)) "projection.center" τ ∧
        Prefix (encodeRational (NativeNodeTolerance.tolerance n D R)) "projection.tolerance" τ)
      (16*(encodeProgram P).length+(36*M.size+124)*N+135) := by
  rintro σ ⟨hc,ht,hp,hlen,hbounded,hinput,hword,hcenter,hword3,htolerance⟩
  obtain ⟨ν,r1,p1⟩ := NativeProgramCache.restore_spec B (encodeProgram P) hLP
    (NativeArrayBounds.prefix_words hbounded hp) σ ⟨hp,hlen,hinput⟩
  have hc1 : NativeProjectionCenter.Context x ν :=
    ⟨(r1.frame_var "vec.n" (by decide)).trans hc.1,
      by simpa only [Prefix,r1.frame_arr "round.center" (by decide)] using hc.2⟩
  obtain ⟨μ,r2,p2⟩ := NativeProjectionCenter.command_spec B M N x hB hshape hscale hx ν
    ⟨hc1,by rw [RamFrames.run_array_length r1]; exact hword,
      by rw [RamFrames.run_array_length r1]; exact hcenter⟩
  have ht2 := NativeNodeTolerance.context_frame (r1.seq r2) ht (by decide) (by decide) (by decide)
  obtain ⟨τ,r3,p3⟩ := NativeNodeTolerance.command_spec B n D R hn hD hR htol μ
    ⟨ht2,by rw [RamFrames.run_array_length r2,RamFrames.run_array_length r1]; exact hword3,
      by rw [RamFrames.run_array_length r2,RamFrames.run_array_length r1]; exact htolerance⟩
  refine ⟨τ,(r1.seq (r2.seq r3)).mono (by nlinarith only []),
    ⟨(r3.frame_var "vec.n" (by decide)).trans p2.1.1,
      by simpa only [Prefix,r3.frame_arr "round.center" (by decide)] using p2.1.2⟩,
    p3.1,?_,?_,p3.2⟩
  · simpa only [Prefix,(r2.seq r3).frame_arr "lp.input" (by decide)] using p1.1
  · simpa only [Prefix,r3.frame_arr "projection.center" (by decide)] using p2.2

end Lax263307Proofs.NativeProjectionPrepare
