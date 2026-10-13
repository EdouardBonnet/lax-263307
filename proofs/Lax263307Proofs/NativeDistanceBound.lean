import Lax263307Proofs.NativeDistanceCoefficient

set_option maxHeartbeats 200000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeDistanceBound

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamRational Lax455465Proofs.RamVirtualState
open Lax455465Proofs.RamFractionPrimitives
open Lax109476.LinearProgram Lax109476.RationalEncoding
open NativeDistanceEntries NativeDistanceCoefficient

def newRows : Com := .seq localRow (.ite (.lt (.var "projection.local") (.var "projection.n"))
  NativeLPRead.center (.seq subtractColumns (.seq NativeLPRead.center negate)))

def command : Com := .ite (.lt (.var "projection.i") (.var "projection.m")) NativeLPRead.bound newRows

def newValue {n : ℕ} (x : Fin n → ℚ) (m i : ℕ) (hi : i < m+(n+n)) (hlo : m ≤ i) : ℚ :=
  if h : i-m < n then x ⟨i-m,h⟩ else -x ⟨i-m-n,by omega⟩

theorem new_rows_spec (B m n : ℕ) (x : Fin n → ℚ) (i : Fin (m+(n+n))) (hlo : m ≤ i.val)
    (hB : 5*m+5*n+20 < B) (hn : ∀ u,(x u).num.natAbs < B) (hd : ∀ u,(x u).den < B) :
    Spec B (fun σ => Prefix (encodeVector x) "projection.center" σ ∧ σ.vars "projection.i"=i.val ∧
      σ.vars "projection.m"=m ∧ σ.vars "projection.n"=n) newRows
      (fun _ τ => FractionOutput (newValue x m i.val i.isLt hlo) τ) 37 := by
  rintro σ ⟨hp,hi,hm,hnv⟩
  have hii := i.isLt
  have hiB : i.val < B := by omega
  have hmB : m < B := by omega
  have hnB : n < B := by omega
  have hlB : i.val-m < B := by omega
  let ν := σ.setVar "projection.local" (i.val-m)
  have r1 : Run B localRow σ ν 4 := Run.assign (evalB_bin (op := .sub)
    (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ hiB⟩)
    (by rw [evalB_var_iff]; exact ⟨hm.symm,hm ▸ hmB⟩) hlB)
  have hloc : ν.vars "projection.local"=i.val-m := by simp [ν]
  have hnv' : ν.vars "projection.n"=n := (r1.frame_var "projection.n" (by decide)).trans hnv
  have hp' : Prefix (encodeVector x) "projection.center" ν := hp
  have hc : (Cond.lt (.var "projection.local") (.var "projection.n")).evalB B ν=some (decide (i.val-m < n)) :=
    evalB_condLt (by rw [evalB_var_iff]; exact ⟨hloc.symm,hloc ▸ hlB⟩)
      (by rw [evalB_var_iff]; exact ⟨hnv'.symm,hnv' ▸ hnB⟩)
  by_cases h : i.val-m < n
  · obtain ⟨τ,r2,p2⟩ := NativeLPRead.center_spec B n x ⟨i.val-m,h⟩ (by omega) (hn _) (hd _) ν ⟨hp',hloc⟩
    have rr := r1.seq (Run.ite_true (b := .lt (.var "projection.local") (.var "projection.n")) (d := .seq subtractColumns (.seq NativeLPRead.center negate)) (by simpa [h] using hc) r2)
    exact ⟨τ,rr.mono (by decide),by simpa only [newValue,dif_pos h] using p2⟩
  · have hj : i.val-m-n < n := by omega
    let μ := ν.setVar "projection.local" (i.val-m-n)
    have r2 : Run B subtractColumns ν μ 4 := Run.assign (evalB_bin (op := .sub)
      (by rw [evalB_var_iff]; exact ⟨hloc.symm,hloc ▸ hlB⟩)
      (by rw [evalB_var_iff]; exact ⟨hnv'.symm,hnv' ▸ hnB⟩) (by change i.val-m-n < B; omega))
    obtain ⟨ξ,r3,p3⟩ := NativeLPRead.center_spec B n x ⟨i.val-m-n,hj⟩ (by omega) (hn _) (hd _) μ
      ⟨hp',by simp [μ]⟩
    obtain ⟨τ,r4,p4⟩ := negate_spec B (x ⟨i.val-m-n,hj⟩) (by omega) ξ p3
    have rr := r1.seq (Run.ite_false (b := .lt (.var "projection.local") (.var "projection.n")) (c := NativeLPRead.center) (by simpa [h] using hc) (r2.seq (r3.seq r4)))
    exact ⟨τ,rr.mono (by decide),by simpa only [newValue,dif_neg h] using p4⟩

theorem command_spec (B m n : ℕ) (P : Program ℚ m n) (x : Fin n → ℚ) (i : Fin (m+(n+n)))
    (hB : 3*(m*n)+5*m+5*n+20 < B)
    (hbn : ∀ u,(P.b u).num.natAbs < B) (hbd : ∀ u,(P.b u).den < B)
    (hxn : ∀ u,(x u).num.natAbs < B) (hxd : ∀ u,(x u).den < B) :
    Spec B (fun σ => Prefix (encodeProgram P) "lp.input" σ ∧ Prefix (encodeVector x) "projection.center" σ ∧
      σ.vars "projection.i"=i.val ∧ σ.vars "projection.m"=m ∧ σ.vars "projection.n"=n) command
      (fun _ τ => FractionOutput (boundEntry P x i.val i.isLt) τ) 50 := by
  rintro σ ⟨hP,hx,hi,hm,hn⟩
  have hiB : i.val < B := by have hh := i.isLt; omega
  have hmB : m < B := by omega
  have hc : (Cond.lt (.var "projection.i") (.var "projection.m")).evalB B σ=some (decide (i.val < m)) :=
    evalB_condLt (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ hiB⟩)
      (by rw [evalB_var_iff]; exact ⟨hm.symm,hm ▸ hmB⟩)
  by_cases h : i.val < m
  · obtain ⟨τ,rr,p⟩ := NativeLPRead.bound_spec B m n P ⟨i.val,h⟩ (by omega) (hbn _) (hbd _) σ ⟨hP,hi,hm,hn⟩
    refine ⟨τ,(Run.ite_true (d := newRows) (by simpa [h] using hc) rr).mono (by decide),?_⟩
    simpa only [boundEntry,dif_pos h] using p
  · obtain ⟨τ,rr,p⟩ := new_rows_spec B m n x i (by omega) (by omega) hxn hxd σ ⟨hx,hi,hm,hn⟩
    refine ⟨τ,(Run.ite_false (c := NativeLPRead.bound) (by simpa [h] using hc) rr).mono (by decide),?_⟩
    have hv : newValue x m i.val i.isLt (by omega)=boundEntry P x i.val i.isLt := by
      unfold newValue boundEntry
      rw [dif_neg h]
      by_cases h' : i.val < m+n
      · have hl : i.val-m < n := by omega
        simp only [dif_pos h',dif_pos hl]
      · have hl : ¬i.val-m < n := by omega
        simp only [dif_neg h',dif_neg hl,Nat.sub_sub]
    simpa only [hv] using p

end Lax263307Proofs.NativeDistanceBound
