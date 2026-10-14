import Lax263307Proofs.NativeCutCoefficient
import Lax455465Proofs.RamVectorEncoding

namespace Lax263307Proofs.NativeCutVector

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.RationalEncoding
open Lax263307.RationalCutBuffer NativeSignedArithmetic NativeCutCoefficient

def command : Com := .seq (.assign "lp.position" (.lit 0))
  (RamVectorEncoding.command "cut.i" "projection.n" NativeCutCoefficient.command)

theorem command_spec (B M n : ℕ) (a : Fin n → ℚ)
    (hB : M*denominator a+M+denominator a+3*n+10<B) (ha : ∀ j,Bounded M (a j)) :
    Spec B (fun σ => Data a σ ∧ 3*n<(σ.arrs "lp.word").length) command
      (fun _ τ => Data a τ ∧ Prefix (encodeVector (fun i => (integerNormal a i : ℚ))) "lp.word" τ ∧
        τ.vars "lp.position"=3*n) (64*n+8) := by
  let values := List.ofFn fun i => (integerNormal a i : ℚ)
  have hnum (i : Fin n) : (integerNormal a i : ℚ).num.natAbs<B := by
    change (NativeScaledInteger.value (a i) (denominator a)).num.natAbs<B
    rw [NativeScaledInteger.magnitude]
    exact (Nat.mul_le_mul (ha i).1 (Nat.div_le_self _ _)).trans_lt (by omega)
  have hden (i : Fin n) : (integerNormal a i : ℚ).den<B := by simp only [Rat.den_intCast]; omega
  have hh := RamVectorEncoding.command_spec B 29 (Data a) "cut.i" "projection.n" values []
    NativeCutCoefficient.command (by omega) (by simp [values]; omega)
    (by intro i hi; simpa only [values,List.getElem_ofFn] using hnum ⟨i,by simpa [values] using hi⟩)
    (by intro i hi; simpa only [values,List.getElem_ofFn] using hden ⟨i,by simpa [values] using hi⟩)
    (fun σ h => by simpa only [values,List.length_ofFn] using h.1.2)
    (fun σ k h => by simpa only [Data,NativeCutRead.Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    (by intro i hi; simpa only [values,List.getElem_ofFn] using NativeCutCoefficient.command_spec B M n a ⟨i,by simpa [values] using hi⟩ hB ha)
    (by decide) (by decide) (by decide) (by decide)
    (fun rr h => frame rr h (by decide) (by decide) (by decide)) (by decide)
  rintro σ ⟨hc,hr⟩
  have r1 : Run B (.assign "lp.position" (.lit 0)) σ (σ.setVar "lp.position" 0) 2 :=
    Run.assign (evalB_lit (by omega))
  obtain ⟨τ,r2,p2⟩ := hh (σ.setVar "lp.position" 0)
    ⟨frame r1 hc (by decide) (by decide) (by decide),by simp [Prefix],by simp,by simpa only [values,List.length_ofFn,List.length_nil,Nat.zero_add,arrs_setVar] using hr⟩
  refine ⟨τ,(r1.seq r2).mono (by simp only [values,List.length_ofFn,Nat.reduceAdd]; omega),p2.1,?_,?_⟩
  · simpa only [List.nil_append,values,RamVectorEncoding.encode,encodeVector] using p2.2.1
  · simpa only [values,List.length_nil,List.length_ofFn,Nat.zero_add] using p2.2.2

end Lax263307Proofs.NativeCutVector
