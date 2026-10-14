import Lax263307Proofs.NativeCertificateRead
import Lax263307Proofs.NativeSignedArithmetic

namespace Lax263307Proofs.NativeProjectionNormal

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.RationalEncoding
open Lax263307.DistanceProjection
open NativeSignedArithmetic

def plus : Com := .seq (.assign "certificate.index" (.add (.var "projection.m") (.var "projection.entry")))
  NativeCertificateRead.dual

def minus : Com := .seq (.assign "certificate.index"
  (.add (.add (.var "projection.m") (.var "projection.n")) (.var "projection.entry")))
  NativeCertificateRead.dual

def command : Com := .seq plus (.seq RamFractionPrimitives.negate (.seq (save "left")
  (.seq minus (.seq (save "right") RamRational.addFraction))))

def Context {m n : ℕ} (z : Fin (n+1) → ℚ) (y : Fin (m+(n+n)) → ℚ) (σ : Env) : Prop :=
  Prefix (encodeCertificate (.optimal z y)) "vm.output" σ ∧
    σ.vars "projection.m"=m ∧ σ.vars "projection.n"=n

theorem frame {m n B K : ℕ} {z : Fin (n+1) → ℚ} {y : Fin (m+(n+n)) → ℚ}
    {σ τ : Env} {c : Com} (rr : Run B c σ τ K) (h : Context z y σ)
    (ha : "vm.output"∉c.warrs) (hm : "projection.m"∉c.wvars) (hn : "projection.n"∉c.wvars) :
    Context z y τ := by
  simpa only [Context,Prefix,rr.frame_arr "vm.output" ha,rr.frame_var "projection.m" hm,
    rr.frame_var "projection.n" hn] using h

theorem plus_spec (B M m n : ℕ) (z : Fin (n+1) → ℚ) (y : Fin (m+(n+n)) → ℚ)
    (i : Fin n) (hB : 2*M^2+3<B) (hs : 3*m+10*n+20<B)
    (hy : ∀ j,Bounded M (y j)) :
    Spec B (fun σ => Context z y σ ∧ σ.vars "projection.entry"=i.val) plus
      (fun _ τ => RamRational.FractionOutput (plusMultipliers y i) τ) 31 := by
  rintro σ ⟨hc,hi⟩
  have hM : M<B := by nlinarith
  let j : Fin (m+(n+n)) := Fin.natAdd m (Fin.castAdd n i)
  have hj : j.val=m+i.val := rfl
  have hset : Run B (.assign "certificate.index" (.add (.var "projection.m") (.var "projection.entry"))) σ
      (σ.setVar "certificate.index" j.val) 4 := by
    apply Run.assign
    rw [hj]
    exact evalB_bin (op := .add)
      (by rw [evalB_var_iff]; exact ⟨hc.2.1.symm,hc.2.1 ▸ (by omega : m<B)⟩)
      (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ (by omega : i.val<B)⟩) (by dsimp only [Bop.apply]; omega)
  obtain ⟨τ,rr,ht⟩ := NativeCertificateRead.dual_spec B m n z y j hs
    ((hy j).1.trans_lt hM) ((hy j).2.trans_lt hM) (σ.setVar "certificate.index" j.val)
    ⟨hc.1,hc.2.2,by simp⟩
  exact ⟨τ,hset.seq rr,ht⟩

theorem minus_spec (B M m n : ℕ) (z : Fin (n+1) → ℚ) (y : Fin (m+(n+n)) → ℚ)
    (i : Fin n) (hB : 2*M^2+3<B) (hs : 3*m+10*n+20<B)
    (hy : ∀ j,Bounded M (y j)) :
    Spec B (fun σ => Context z y σ ∧ σ.vars "projection.entry"=i.val) minus
      (fun _ τ => RamRational.FractionOutput (minusMultipliers y i) τ) 33 := by
  rintro σ ⟨hc,hi⟩
  have hM : M<B := by nlinarith
  let j : Fin (m+(n+n)) := Fin.natAdd m (Fin.natAdd n i)
  have hj : j.val=(m+n)+i.val := by dsimp [j]; omega
  have hset : Run B (.assign "certificate.index" (.add (.add (.var "projection.m") (.var "projection.n")) (.var "projection.entry"))) σ
      (σ.setVar "certificate.index" j.val) 6 := by
    apply Run.assign
    rw [hj]
    exact evalB_bin (op := .add)
      (evalB_bin (op := .add)
        (by rw [evalB_var_iff]; exact ⟨hc.2.1.symm,hc.2.1 ▸ (by omega : m<B)⟩)
        (by rw [evalB_var_iff]; exact ⟨hc.2.2.symm,hc.2.2 ▸ (by omega : n<B)⟩) (by dsimp only [Bop.apply]; omega))
      (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ (by omega : i.val<B)⟩) (by dsimp only [Bop.apply]; omega)
  obtain ⟨τ,rr,ht⟩ := NativeCertificateRead.dual_spec B m n z y j hs
    ((hy j).1.trans_lt hM) ((hy j).2.trans_lt hM) (σ.setVar "certificate.index" j.val)
    ⟨hc.1,hc.2.2,by simp⟩
  exact ⟨τ,hset.seq rr,ht⟩

theorem command_spec (B M m n : ℕ) (z : Fin (n+1) → ℚ) (y : Fin (m+(n+n)) → ℚ)
    (i : Fin n) (hB : 2*M^2+3<B) (hs : 3*m+10*n+20<B)
    (hy : ∀ j,Bounded M (y j)) :
    Spec B (fun σ => Context z y σ ∧ σ.vars "projection.entry"=i.val) command
      (fun _ τ => Context z y τ ∧ RamRational.FractionOutput (normal y i) τ)
      (36*(M^2).size+176) := by
  rintro σ ⟨hc,hi⟩
  have h1 : 1<B := by nlinarith
  have hM : M<B := by nlinarith
  have hp : Bounded M (plusMultipliers y i) := hy _
  have hm : Bounded M (minusMultipliers y i) := hy _
  have hpneg : Bounded M (-plusMultipliers y i) := by
    simpa only [Bounded,Rat.neg_num,Int.natAbs_neg,Rat.neg_den] using hp
  obtain ⟨σ1,r1,p1⟩ := plus_spec B M m n z y i hB hs hy σ ⟨hc,hi⟩
  obtain ⟨σ2,r2,p2⟩ := RamFractionPrimitives.negate_spec B (plusMultipliers y i) h1 σ1 p1
  obtain ⟨σ3,r3,p3⟩ := save_spec B "left" (-plusMultipliers y i) h1
    (hpneg.1.trans_lt hM) (hpneg.2.trans_lt hM) (by decide) σ2 p2
  have r123 := r1.seq (r2.seq r3)
  obtain ⟨σ4,r4,p4⟩ := minus_spec B M m n z y i hB hs hy σ3
    ⟨frame r123 hc (by decide) (by decide) (by decide),
      (r123.frame_var "projection.entry" (by decide)).trans hi⟩
  obtain ⟨σ5,r5,p5⟩ := save_spec B "right" (minusMultipliers y i) h1
    (hm.1.trans_lt hM) (hm.2.trans_lt hM) (by decide) σ4 p4
  have hleft : Stored "left" (-plusMultipliers y i) σ5 := by
    simpa only [Stored,String.reduceAppend,(r4.seq r5).frame_var "left.s" (by decide),
      (r4.seq r5).frame_var "left.n" (by decide),(r4.seq r5).frame_var "left.d" (by decide)] using p3
  obtain ⟨τ,r6,p6⟩ := add_spec B M (-plusMultipliers y i) (minusMultipliers y i) hB hpneg hm σ5 ⟨hleft,p5⟩
  have hden : ((-plusMultipliers y i).den*(minusMultipliers y i).den).size≤(M^2).size :=
    Nat.size_le_size (by nlinarith [Nat.mul_le_mul hpneg.2 hm.2])
  have rr := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6))))
  refine ⟨τ,rr.mono (by omega),frame rr hc (by decide) (by decide) (by decide),?_⟩
  simpa only [normal,sub_eq_neg_add] using p6

end Lax263307Proofs.NativeProjectionNormal
