import Lax263307Proofs.NativeProjectionNormal
import Lax263307Proofs.NativeRationalBounds
import Lax455465Proofs.RamVectorEncoding

namespace Lax263307Proofs.NativeProjectionVectors

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.RationalEncoding
open Lax263307.DistanceProjection NativeSignedArithmetic
open NativeProjectionNormal

def normalCommand : Com := .seq (.assign "lp.position" (.lit 0))
  (RamVectorEncoding.command "projection.entry" "projection.n" NativeProjectionNormal.command)

theorem normal_spec (B M m n : ℕ) (z : Fin (n+1) → ℚ) (y : Fin (m+(n+n)) → ℚ)
    (hB : 2*M^2+3<B) (hs : 3*m+10*n+20<B) (hy : ∀ j,Bounded M (y j)) :
    Spec B (fun σ => Context z y σ ∧ 3*n<(σ.arrs "lp.word").length) normalCommand
      (fun _ τ => Context z y τ ∧ Prefix (encodeVector (normal y)) "lp.word" τ ∧
        τ.vars "lp.position"=3*n) ((36*(M^2).size+211)*n+8) := by
  have h1 : 1<B := by nlinarith
  have hheight (i : Fin n) : Bounded (2*M^2) (normal y i) :=
    NativeRationalBounds.subtract M (minusMultipliers y i) (plusMultipliers y i) (hy _) (hy _)
  have hh := RamVectorEncoding.command_spec B (36*(M^2).size+176) (Context z y)
    "projection.entry" "projection.n" (List.ofFn (normal y)) [] NativeProjectionNormal.command h1
    (by simp; omega)
    (by intro i hi; simp only [List.getElem_ofFn]; exact (hheight ⟨i,by simpa using hi⟩).1.trans_lt (by omega))
    (by intro i hi; simp only [List.getElem_ofFn]; exact (hheight ⟨i,by simpa using hi⟩).2.trans_lt (by omega))
    (fun σ h => by simpa only [List.length_ofFn] using h.2.2)
    (fun σ k h => by simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    (by intro i hi; simpa only [List.getElem_ofFn] using NativeProjectionNormal.command_spec B M m n z y ⟨i,by simpa using hi⟩ hB hs hy)
    (by decide) (by decide) (by decide) (by decide)
    (fun rr h => frame rr h (by decide) (by decide) (by decide)) (by decide)
  rintro σ ⟨hc,hr⟩
  have r1 : Run B (.assign "lp.position" (.lit 0)) σ (σ.setVar "lp.position" 0) 2 :=
    Run.assign (evalB_lit (by omega))
  obtain ⟨τ,r2,p2⟩ := hh (σ.setVar "lp.position" 0)
    ⟨frame r1 hc (by decide) (by decide) (by decide),by simp [Prefix],by simp,by simpa using hr⟩
  refine ⟨τ,(r1.seq r2).mono (by simp only [List.length_ofFn,Nat.add_assoc,Nat.reduceAdd]; omega),p2.1,?_,?_⟩
  · simpa only [List.nil_append,RamVectorEncoding.encode,encodeVector] using p2.2.1
  · simpa only [List.length_nil,List.length_ofFn,Nat.zero_add] using p2.2.2

end Lax263307Proofs.NativeProjectionVectors
