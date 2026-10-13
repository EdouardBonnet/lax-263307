import Lax263307Proofs.NativeLPRead
import Lax263307Proofs.NativeDistanceEntries
import Lax263307Proofs.NativeDistanceUnits

set_option maxHeartbeats 200000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeDistanceCoefficient

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamRational Lax455465Proofs.RamVirtualState
open Lax455465Proofs.RamFractionPrimitives
open Lax109476.LinearProgram Lax109476.RationalEncoding
open NativeDistanceEntries NativeDistanceUnits

def oldRow : Com := .ite (.lt (.var "projection.j") (.var "projection.n")) NativeLPRead.matrix zero

def oldValue {m n : ℕ} (P : Program ℚ m n) (i : Fin m) (j : ℕ) : ℚ :=
  if hj : j < n then P.A i ⟨j,hj⟩ else 0

theorem old_row_spec (B m n : ℕ) (P : Program ℚ m n) (i : Fin m) (j : Fin (n+1))
    (hB : 3*(m*n)+3*m+3*n+20 < B)
    (hn : ∀ u v,(P.A u v).num.natAbs < B) (hd : ∀ u v,(P.A u v).den < B) :
    Spec B (fun σ => Prefix (encodeProgram P) "lp.input" σ ∧ σ.vars "projection.i"=i.val ∧
      σ.vars "projection.j"=j.val ∧ σ.vars "projection.n"=n) oldRow
      (fun _ τ => FractionOutput (oldValue P i j.val) τ) 31 := by
  rintro σ ⟨hp,hi,hj,hnv⟩
  have hjB : j.val < B := by have hh := j.isLt; omega
  have hnB : n < B := by omega
  have hc : (Cond.lt (.var "projection.j") (.var "projection.n")).evalB B σ=some (decide (j.val < n)) :=
    evalB_condLt (by rw [evalB_var_iff]; exact ⟨hj.symm,hj ▸ hjB⟩)
      (by rw [evalB_var_iff]; exact ⟨hnv.symm,hnv ▸ hnB⟩)
  by_cases h : j.val < n
  · obtain ⟨τ,rr,p⟩ := NativeLPRead.matrix_spec B m n P i ⟨j.val,h⟩ (by omega) (hn _ _) (hd _ _) σ ⟨hp,hi,hj,hnv⟩
    exact ⟨τ,Run.ite_true (d := zero) (by simpa [h] using hc) rr,by simpa only [oldValue,dif_pos h] using p⟩
  · obtain ⟨τ,rr,p⟩ := zero_spec B (by omega) σ trivial
    exact ⟨τ,(Run.ite_false (c := NativeLPRead.matrix) (by simpa [h] using hc) rr).mono (by decide),by simpa only [oldValue,dif_neg h] using p⟩

def localRow : Com := .assign "projection.local" (.sub (.var "projection.i") (.var "projection.m"))
def subtractColumns : Com := .assign "projection.local" (.sub (.var "projection.local") (.var "projection.n"))

def newRows : Com := .seq localRow (.ite (.lt (.var "projection.local") (.var "projection.n"))
  (extended false) (.seq subtractColumns (extended true)))

def command : Com := .ite (.lt (.var "projection.i") (.var "projection.m")) oldRow newRows

def newValue (m n i j : ℕ) : ℚ :=
  if i < m+n then extendedValue false n (i-m) j else extendedValue true n (i-(m+n)) j

theorem new_rows_spec (B m n : ℕ) (i : Fin (m+(n+n))) (j : Fin (n+1)) (hlo : m ≤ i.val)
    (hB : 3*(m*n)+5*m+5*n+20 < B) :
    Spec B (fun σ => σ.vars "projection.i"=i.val ∧ σ.vars "projection.m"=m ∧
      σ.vars "projection.n"=n ∧ σ.vars "projection.j"=j.val) newRows
      (fun _ τ => FractionOutput (newValue m n i.val j.val) τ) 26 := by
  have hi := i.isLt
  have hj := j.isLt
  have hsub : i.val-m ≤ i.val := Nat.sub_le _ _
  have hsub' : i.val-m-n ≤ i.val := (Nat.sub_le _ _).trans hsub
  have hpos := extended_spec B false n (i.val-m) j.val (by omega)
  have hneg := extended_spec B true n (i.val-m-n) j.val (by omega)
  by_cases h : i.val < m+n
  · have hl : i.val-m < n := by omega
    run_vcg [hpos,hneg]
    all_goals simp_all [newValue,Nat.sub_sub,Env.setVar]
  · have hl : ¬i.val-m < n := by omega
    have hv : newValue m n i.val j.val=extendedValue true n (i.val-m-n) j.val := by
      simp [newValue,h,Nat.sub_sub]
    run_vcg [hpos,hneg]
    all_goals simp_all [Nat.sub_sub,Env.setVar]
    all_goals omega

theorem command_spec (B m n : ℕ) (P : Program ℚ m n) (i : Fin (m+(n+n))) (j : Fin (n+1))
    (hB : 3*(m*n)+5*m+5*n+20 < B)
    (hn : ∀ u v,(P.A u v).num.natAbs < B) (hd : ∀ u v,(P.A u v).den < B) :
    Spec B (fun σ => Prefix (encodeProgram P) "lp.input" σ ∧ σ.vars "projection.i"=i.val ∧
      σ.vars "projection.m"=m ∧ σ.vars "projection.n"=n ∧ σ.vars "projection.j"=j.val) command
      (fun _ τ => FractionOutput (matrixEntry P i.val j.val) τ) 40 := by
  rintro σ ⟨hp,hi,hm,hnv,hj⟩
  have hiB : i.val < B := by have hh := i.isLt; omega
  have hmB : m < B := by omega
  have hc : (Cond.lt (.var "projection.i") (.var "projection.m")).evalB B σ=some (decide (i.val < m)) :=
    evalB_condLt (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ hiB⟩)
      (by rw [evalB_var_iff]; exact ⟨hm.symm,hm ▸ hmB⟩)
  by_cases h : i.val < m
  · obtain ⟨τ,rr,p⟩ := old_row_spec B m n P ⟨i.val,h⟩ j (by omega) hn hd σ ⟨hp,hi,hj,hnv⟩
    refine ⟨τ,(Run.ite_true (d := newRows) (by simpa [h] using hc) rr).mono (by decide),?_⟩
    simpa only [matrixEntry,dif_pos h,oldValue] using p
  · obtain ⟨τ,rr,p⟩ := new_rows_spec B m n i j (by omega) hB σ ⟨hi,hm,hnv,hj⟩
    refine ⟨τ,(Run.ite_false (c := oldRow) (by simpa [h] using hc) rr).mono (by decide),?_⟩
    simpa only [matrixEntry,dif_neg h,newValue,extendedValue,matchingValue,unitValue,Bool.false_eq_true,if_false,if_true] using p

end Lax263307Proofs.NativeDistanceCoefficient
