import Lax263307Proofs.NativeChildLift

namespace Lax263307Proofs.NativeChildReturn

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators NativeMasks

def setup : Com := .seq (.assign "lift.parent.n" (.var "graph.n"))
  (.seq (.assign "graph.n" (.var "restrict.count"))
    (.assign "unpack.mask" (.var "recursion.return.mask")))

def liftCommand : Com := .seq setup (.seq NativeMaskUnpack.command
  (.seq NativeChildLift.command (.assign "graph.n" (.var "lift.parent.n"))))

theorem setup_spec (B n r m : ℕ) (hn : n<B) (hr : r<B) (hm : m<B) :
    Spec B (fun σ => σ.vars "graph.n"=n ∧ σ.vars "restrict.count"=r ∧ σ.vars "recursion.return.mask"=m) setup
      (fun _ τ => τ.vars "lift.parent.n"=n ∧ τ.vars "graph.n"=r ∧ τ.vars "unpack.mask"=m) 6 := by
  rintro σ ⟨hnσ,hrσ,hmσ⟩
  run_vcg
  all_goals simp_all [Env.setVar]

/-- Decode and lift a returned child mask after its parent's frame has
been restored. The parent graph order is restored after the decoding. -/
theorem lift_spec (B n : ℕ) (R : Finset (Fin n)) (I : Finset (Fin R.card))
    (hB : n+2<B) (hm : 2^n<B) :
    Spec B (fun σ => σ.vars "graph.n"=n ∧ σ.vars "restrict.count"=R.card ∧
      σ.vars "recursion.return.mask"=mask I ∧ Prefix (NativeRestrictionOrder.words R) "restrict.vertices" σ ∧
      R.card≤(σ.arrs "subset.bits").length) liftCommand
      (fun _ τ => τ.vars "graph.n"=n ∧ τ.vars "lift.mask"=mask (I.image (label R)) ∧
        Prefix (NativeRestrictionOrder.words R) "restrict.vertices" τ) (45*R.card+24) := by
  have hr := NativeMaskUnpack.card_bound R
  have hmR : 2^R.card<B := (Nat.pow_le_pow_right (by decide) hr).trans_lt hm
  rintro σ ⟨hn,hcount,hmask,hlabels,hroom⟩
  obtain ⟨ν,r1,p1⟩ := setup_spec B n R.card (mask I) (by omega) (by omega) ((mask_bound I).trans hmR)
    σ ⟨hn,hcount,hmask⟩
  obtain ⟨μ,r2,p2⟩ := NativeMaskUnpack.command_spec B I (by omega) hmR ν
    ⟨p1.2.1,p1.2.2,by rwa [RamFrames.run_array_length r1]⟩
  have rr := r1.seq r2
  obtain ⟨ρ,r3,p3⟩ := NativeChildLift.command_spec B n R I hB hm μ
    ⟨(r2.frame_var "graph.n" (by decide)).trans p1.2.1,p2.1,
      by simpa only [Prefix,rr.frame_arr "restrict.vertices" (by decide)] using hlabels⟩
  have hparent := ((r2.seq r3).frame_var "lift.parent.n" (by decide)).trans p1.1
  let τ := ρ.setVar "graph.n" n
  have r4 : Run B (.assign "graph.n" (.var "lift.parent.n")) ρ τ 2 := Run.assign
    (by rw [evalB_var_iff]; exact ⟨hparent.symm,hparent ▸ (by omega : n<B)⟩)
  exact ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono (by omega),by simp [τ],
    (r4.frame_var "lift.mask" (by decide)).trans p3.2,
    by simpa only [Prefix,τ,arrs_setVar] using p3.1.labels⟩

def command : Com := .ite (.eq (.var "recursion.return.tag") (.lit 1)) liftCommand
  (.assign "lift.mask" (.lit 0))


end Lax263307Proofs.NativeChildReturn
