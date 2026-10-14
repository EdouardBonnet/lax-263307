import Lax263307Proofs.NativeClearNormal
import Lax263307Proofs.NativeCutResources
import Lax263307Proofs.NativeProjectionResult

set_option maxRecDepth 10000
set_option maxHeartbeats 400000

namespace Lax263307Proofs.NativeProjectionCut

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax263307.RationalProjection Lax263307.RationalCutBuffer NativeSignedArithmetic

/-- The projection result after the far branch's denominator clearing. -/
def Output {n : ℕ} : Outcome n → Env → Prop
  | .near x, σ => σ.vars "projection.kind"=0 ∧ Prefix (encodeVector x) "lp.word" σ ∧ σ.vars "lp.position"=3*n
  | .far a _, σ => σ.vars "projection.kind"=1 ∧
      Prefix (encodeVector (fun i => (integerNormal a i : ℚ))) "lp.word" σ ∧ σ.vars "lp.position"=3*n
  | .reject, σ => σ.vars "projection.kind"=2

def Guard (B M : ℕ) {n : ℕ} : Outcome n → Prop
  | .far a _ => M*denominator a+M+denominator a+3*n+10<B ∧ ∀ i,Bounded M (a i)
  | _ => True

def finish : Com := .ite (.eq (.var "projection.kind") (.lit 1)) NativeClearNormal.command .skip

def command : Com := .seq NativeDistanceMetadata.readDimensions finish

theorem command_spec (B M m n : ℕ) (P : Program ℚ m n) (o : Outcome n)
    (hs : m+n+3<B) (hg : Guard B M o) :
    Spec B (fun σ => Prefix (encodeProgram P) "lp.input" σ ∧ NativeProjectionResult.Output o σ ∧
      3*n≤(σ.arrs "cut.source").length ∧ 3*n<(σ.arrs "lp.word").length) command
      (fun _ τ => Output o τ ∧ Prefix (encodeProgram P) "lp.input" τ)
      (145*n+38) := by
  rintro σ ⟨hp,ho,hS,hO⟩
  obtain ⟨ν,r1,p1⟩ := NativeDistanceMetadata.read_dimensions_spec B m n P hs σ hp
  have hoν : NativeProjectionResult.Output o ν := by
    cases o <;> simpa only [NativeProjectionResult.Output,Prefix,r1.frame_var "projection.kind" (by decide),
      r1.frame_var "lp.position" (by decide),r1.frame_arr "lp.word" (by decide)] using ho
  have hpν : Prefix (encodeProgram P) "lp.input" ν := by
    simpa only [Prefix,r1.frame_arr "lp.input" (by decide)] using hp
  cases o with
  | near x =>
    have hh := hoν.1
    have he : (Cond.eq (.var "projection.kind") (.lit 1)).evalB B ν=some false := by
      rw [evalB_condEq (by rw [evalB_var_iff]; exact ⟨hh.symm,hh ▸ (by omega : 0<B)⟩) (evalB_lit (by omega : 1<B))]
      rfl
    have r2 : Run B finish ν ν 5 := Run.ite_false he Run.skip
    exact ⟨ν,(r1.seq r2).mono (by omega),hoν,hpν⟩
  | far a bound =>
    obtain ⟨τ,r2,p2⟩ := NativeClearNormal.command_spec B M n a hg.1 hg.2 ν
      ⟨hoν.2.1,p1.2,by rwa [RamFrames.run_array_length r1],by rwa [RamFrames.run_array_length r1]⟩
    have hh := hoν.1
    have he : (Cond.eq (.var "projection.kind") (.lit 1)).evalB B ν=some true := by
      rw [evalB_condEq (by rw [evalB_var_iff]; exact ⟨hh.symm,hh ▸ (by omega : 1<B)⟩) (evalB_lit (by omega : 1<B))]
      rfl
    have rr := r1.seq (Run.ite_true (d := .skip) he r2)
    exact ⟨τ,rr.mono (by dsimp [Cond.size,Expr.size]; omega),
      ⟨(r2.frame_var "projection.kind" (by decide)).trans hh,p2.1,p2.2.1⟩,
      by simpa only [Prefix,rr.frame_arr "lp.input" (by decide)] using hp⟩
  | reject =>
    have he : (Cond.eq (.var "projection.kind") (.lit 1)).evalB B ν=some false := by
      rw [evalB_condEq (by rw [evalB_var_iff]; exact ⟨hoν.symm,hoν ▸ (by omega : 2<B)⟩) (evalB_lit (by omega : 1<B))]
      rfl
    have r2 : Run B finish ν ν 5 := Run.ite_false he Run.skip
    exact ⟨ν,(r1.seq r2).mono (by omega),hoν,hpν⟩

end Lax263307Proofs.NativeProjectionCut
