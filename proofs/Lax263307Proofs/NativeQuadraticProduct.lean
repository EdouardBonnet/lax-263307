import Lax263307Proofs.NativeCutRead
import Lax263307Proofs.NativeBlowUp
import Lax263307Proofs.NativeSumHeight

namespace Lax263307Proofs.NativeQuadraticProduct

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamRational Lax455465Proofs.RamVirtualState
open NativeSignedArithmetic NativeCutRead

def row : Com := .assign "cut.i" (.div (.var "quadratic.i") (.var "projection.n"))

def col : Com := .assign "cut.i" (.sub (.var "quadratic.i")
  (.mul (.div (.var "quadratic.i") (.var "projection.n")) (.var "projection.n")))

theorem row_spec (B n : ℕ) (i : Fin (n*n)) (hB : n*n+n+3<B) :
    Spec B (fun σ => σ.vars "quadratic.i"=i.val ∧ σ.vars "projection.n"=n) row
      (fun _ τ => τ.vars "cut.i"=(NativeBlowUp.row i).val) 4 := by
  have hn : 0<n := by nlinarith only [i.isLt]
  have hi := i.isLt
  have hd : i.val/n<n := (Nat.div_lt_iff_lt_mul hn).mpr hi
  run_vcg
  all_goals simp_all [NativeBlowUp.row]
  all_goals omega

theorem col_spec (B n : ℕ) (i : Fin (n*n)) (hB : n*n+n+3<B) :
    Spec B (fun σ => σ.vars "quadratic.i"=i.val ∧ σ.vars "projection.n"=n) col
      (fun _ τ => τ.vars "cut.i"=(NativeBlowUp.col i).val) 8 := by
  have hn : 0<n := by nlinarith only [i.isLt]
  have hi := i.isLt
  have hd : i.val/n<n := (Nat.div_lt_iff_lt_mul hn).mpr hi
  have hp := Nat.div_mul_le_self i.val n
  have hm : i.val%n=i.val-(i.val/n)*n := by
    exact Nat.mod_eq_sub_div_mul
  run_vcg
  all_goals simp_all [NativeBlowUp.col]
  all_goals omega

def command : Com := .seq row (.seq NativeCutRead.command (.seq (save "left")
  (.seq col (.seq NativeCutRead.command (.seq (save "right") multiplyFraction)))))

/-- Read both coordinates of a flattened ordered vertex pair and
multiply their actual rational encodings. -/
theorem command_spec (B M n : ℕ) (a : Fin n → ℚ) (i : Fin (n*n))
    (hB : 2*M^2+3<B) (hs : n*n+3*n+10<B) (ha : ∀ j,Bounded M (a j)) :
    Spec B (fun σ => Context a σ ∧ σ.vars "quadratic.i"=i.val) command
      (fun _ τ => Context a τ ∧ FractionOutput (a (NativeBlowUp.row i)*a (NativeBlowUp.col i)) τ)
      (36*(M^2).size+130) := by
  have h1 : 1<B := by nlinarith
  have hM : M<B := by nlinarith
  rintro σ ⟨hc,hi⟩
  obtain ⟨σ1,r1,p1⟩ := row_spec B n i (by omega) σ ⟨hi,hc.2⟩
  have hc1 : Context a σ1 := by
    simpa only [Context,Prefix,r1.frame_arr "cut.source" (by decide),r1.frame_var "projection.n" (by decide)] using hc
  obtain ⟨σ2,r2,p2⟩ := NativeCutRead.command_spec B M n a (NativeBlowUp.row i) hM (by omega) ha σ1 ⟨hc1,p1⟩
  obtain ⟨σ3,r3,p3⟩ := save_spec B "left" (a (NativeBlowUp.row i)) h1
    ((ha _).1.trans_lt hM) ((ha _).2.trans_lt hM) (by decide) σ2 p2.2
  have r123 := r1.seq (r2.seq r3)
  have hc3 : Context a σ3 := by
    simpa only [Context,Prefix,r123.frame_arr "cut.source" (by decide),r123.frame_var "projection.n" (by decide)] using hc
  obtain ⟨σ4,r4,p4⟩ := col_spec B n i (by omega) σ3
    ⟨(r123.frame_var "quadratic.i" (by decide)).trans hi,hc3.2⟩
  have hc4 : Context a σ4 := by
    simpa only [Context,Prefix,r4.frame_arr "cut.source" (by decide),r4.frame_var "projection.n" (by decide)] using hc3
  obtain ⟨σ5,r5,p5⟩ := NativeCutRead.command_spec B M n a (NativeBlowUp.col i) hM (by omega) ha σ4 ⟨hc4,p4⟩
  obtain ⟨σ6,r6,p6⟩ := save_spec B "right" (a (NativeBlowUp.col i)) h1
    ((ha _).1.trans_lt hM) ((ha _).2.trans_lt hM) (by decide) σ5 p5.2
  have hleft : Stored "left" (a (NativeBlowUp.row i)) σ6 := by
    simpa only [Stored,String.reduceAppend,(r4.seq (r5.seq r6)).frame_var "left.s" (by decide),
      (r4.seq (r5.seq r6)).frame_var "left.n" (by decide),
      (r4.seq (r5.seq r6)).frame_var "left.d" (by decide)] using p3
  obtain ⟨τ,r7,p7⟩ := multiply_spec B M (a (NativeBlowUp.row i)) (a (NativeBlowUp.col i)) hB
    (ha _) (ha _) σ6 ⟨hleft,p6⟩
  have hden : ((a (NativeBlowUp.row i)).den*(a (NativeBlowUp.col i)).den).size≤(M^2).size :=
    Nat.size_le_size (by nlinarith [Nat.mul_le_mul (ha (NativeBlowUp.row i)).2 (ha (NativeBlowUp.col i)).2])
  have rr := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))
  refine ⟨τ,rr.mono (by omega),?_,p7⟩
  simpa only [Context,Prefix,rr.frame_arr "cut.source" (by decide),rr.frame_var "projection.n" (by decide)] using hc

end Lax263307Proofs.NativeQuadraticProduct
