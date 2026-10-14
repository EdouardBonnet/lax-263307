import Lax263307Proofs.NativeCutRead
import Lax263307Proofs.NativeScaledInteger
import Lax263307Proofs.NativeDenominatorData

namespace Lax263307Proofs.NativeCutCoefficient

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamRational Lax455465Proofs.RamVirtualState
open Lax263307.RationalCutBuffer NativeSignedArithmetic NativeCutRead

def command : Com := .seq NativeCutRead.command NativeScaledInteger.command

def Data {n : ℕ} (a : Fin n → ℚ) (σ : Env) : Prop :=
  Context a σ ∧ σ.vars "cut.denominator"=denominator a

theorem frame {n B K : ℕ} {a : Fin n → ℚ} {σ τ : Env} {c : Com}
    (rr : Run B c σ τ K) (h : Data a σ) (hsource : "cut.source"∉c.warrs)
    (hN : "projection.n"∉c.wvars) (hD : "cut.denominator"∉c.wvars) : Data a τ := by
  simpa only [Data,Context,Prefix,rr.frame_arr "cut.source" hsource,
    rr.frame_var "projection.n" hN,rr.frame_var "cut.denominator" hD] using h

theorem command_spec (B M n : ℕ) (a : Fin n → ℚ) (i : Fin n)
    (hB : M*denominator a+M+denominator a+3*n+10<B) (ha : ∀ j,Bounded M (a j)) :
    Spec B (fun σ => Data a σ ∧ σ.vars "cut.i"=i.val) command
      (fun _ τ => Data a τ ∧ FractionOutput (integerNormal a i : ℚ) τ) 29 := by
  rintro σ ⟨hc,hi⟩
  obtain ⟨ν,r1,p1⟩ := NativeCutRead.command_spec B M n a i (by omega) (by omega) ha σ ⟨hc.1,hi⟩
  obtain ⟨τ,r2,p2⟩ := NativeScaledInteger.command_spec B M (denominator a) (a i)
    (by omega) (by omega) (by omega) (by omega) (ha i) ν
    ⟨p1.2,(r1.frame_var "cut.denominator" (by decide)).trans hc.2⟩
  have rr := r1.seq r2
  exact ⟨τ,rr,frame rr hc (by decide) (by decide) (by decide),p2⟩

end Lax263307Proofs.NativeCutCoefficient
