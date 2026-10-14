import Lax263307Proofs.NativeNodePrecision
import Lax263307Proofs.NativeProgramCache
import Lax263307Proofs.NativeRoundedInitial
import Lax263307Proofs.NativeMomentInput
import Lax263307Proofs.NativeArrayBounds

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeLargeSetup

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 MomentLP RoundedOracleSearch

def command : Com := .seq NativeMomentInput.command (.seq NativeProgramCache.save
  (.seq NativeNodePrecision.command NativeRoundedInitial.command))

def timeBound (n r : ℕ) : ℕ := NativeMomentInput.cost n r+16*NativeMomentInput.length n r+
  12*r+105*(dimension n r*dimension n r)+91*dimension n r+108

theorem family_frame {B n k r t : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {σ τ : Env} (rr : Run B (.seq NativeProgramCache.save
      (.seq NativeNodePrecision.command NativeRoundedInitial.command)) σ τ t)
    (hs : NativeMomentFamily.Data G k r σ) : NativeMomentFamily.Data G k r τ := by
  apply NativeMomentFamily.data_frame G k r rr ?_ ?_ hs
  · intro s hs
    simp [NativeMomentFamily.fixedVars] at hs
    rcases hs with rfl|rfl|rfl|rfl <;> decide
  · intro s hs
    simp [NativeMomentFamily.fixedArrays] at hs
    rcases hs with rfl|rfl|rfl|rfl <;> decide

theorem precision_frame {B n D N b r t : ℕ} {σ τ : Env}
    (rr : Run B NativeRoundedInitial.command σ τ t) (hs : NativeNodePrecision.Output n D N b r σ) :
    NativeNodePrecision.Output n D N b r τ := by
  refine ⟨NativeNodePrecision.context_frame rr hs.1 (by decide) (by decide) (by decide) (by decide) (by decide),
    (rr.frame_var "node.floorPower" (by decide)).trans hs.2.1,
    (rr.frame_var "node.radius" (by decide)).trans hs.2.2.1,
    (rr.frame_var "node.precision" (by decide)).trans hs.2.2.2.1,
    (rr.frame_var "round.limit" (by decide)).trans hs.2.2.2.2.1,
    (rr.frame_var "vec.n" (by decide)).trans hs.2.2.2.2.2⟩

/-- The complete nonrecursive large-node initialization phase: build
and cache its actual moment LP, compute its numeric search budgets,
+and materialize the initial rounded state. -/
theorem command_spec {n : ℕ} (B : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k r D b : ℕ) (hb : 1≤b)
    (hLP : NativeMomentInput.length n r+n+k+r+dimension n r+10<B) (hm : 2^n<B)
    (hprec : NativeNodePrecision.guard n D (dimension n r) b r<B)
    (hround : 3*(dimension n r*dimension n r)+3*dimension n r+20<B) :
    Spec B (fun σ => NativeMomentFamily.Data G k r σ ∧
      NativeNodePrecision.Context n D (dimension n r) b r σ ∧ NativeArrayBounds.Bounded B σ ∧
      NativeMomentInput.length n r≤(σ.arrs "lp.input").length ∧
      NativeMomentInput.length n r≤(σ.arrs "moment.program").length ∧
      3*(dimension n r*dimension n r)+3*dimension n r≤(σ.arrs "lp.input").length ∧
      3*(dimension n r*dimension n r)≤(σ.arrs "round.shape").length ∧
      3*dimension n r≤(σ.arrs "round.center").length) command
      (fun _ τ => NativeMomentFamily.Data G k r τ ∧
        Prefix (encodeProgram (MomentLP.program G k r)) "moment.program" τ ∧
        τ.vars "node.programLength"=NativeMomentInput.length n r ∧
        NativeNodePrecision.Output n D (dimension n r) b r τ ∧
        Prefix (NativeRoundedQuery.shape ((1,0) : State (dimension n r))) "round.shape" τ ∧
        Prefix (NativeRoundedQuery.center ((1,0) : State (dimension n r))) "round.center" τ ∧
        τ.vars "round.i"=0) (timeBound n r) := by
  have hlen := NativeMomentInput.input_length G k r
  rintro σ ⟨hd,hctx,hbounded,hinput,hcache,hroundinput,hshape,hcenter⟩
  obtain ⟨ν,r1,p1⟩ := NativeMomentInput.command_spec B G k r hLP hm σ ⟨hd,hinput⟩
  have hw := NativeArrayBounds.prefix_words (NativeArrayBounds.run r1 hbounded) p1.2.2
  obtain ⟨μ,r2,p2⟩ := NativeProgramCache.save_spec B (encodeProgram (MomentLP.program G k r))
    (by rw [hlen]; omega) hw ν
    ⟨p1.2.2,by rw [hlen]; exact p1.2.1,by rw [hlen,RamFrames.run_array_length r1]; exact hcache⟩
  have hctx2 := NativeNodePrecision.context_frame (r1.seq r2) hctx (by decide) (by decide)
    (by decide) (by decide) (by decide)
  obtain ⟨ρ,r3,p3⟩ := NativeNodePrecision.command_spec B n D (dimension n r) b r hb hprec μ hctx2
  obtain ⟨τ,r4,p4⟩ := NativeRoundedInitial.command_spec B (dimension n r) hround ρ
    ⟨p3.2.2.2.2.2,
      by rw [RamFrames.run_array_length r3,RamFrames.run_array_length r2,RamFrames.run_array_length r1]; exact hroundinput,
      by rw [RamFrames.run_array_length r3,RamFrames.run_array_length r2,RamFrames.run_array_length r1]; exact hshape,
      by rw [RamFrames.run_array_length r3,RamFrames.run_array_length r2,RamFrames.run_array_length r1]; exact hcenter⟩
  refine ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono ?_,family_frame (r2.seq (r3.seq r4)) p1.1,
    ?_,?_,precision_frame r4 p3,p4.2⟩
  · rw [hlen]
    dsimp only [timeBound]
    nlinarith only []
  · simpa only [Prefix,(r3.seq r4).frame_arr "moment.program" (by decide)] using p2.1
  · exact ((r3.seq r4).frame_var "node.programLength" (by decide)).trans (by simpa only [hlen] using p2.2)

end Lax263307Proofs.NativeLargeSetup
