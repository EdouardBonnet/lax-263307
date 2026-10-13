import Lax263307.DistanceProjection
import Lax263307Proofs.NativeMomentAssembly

/-! Explicit runtime-index forms of the distance LP's matrix and vectors.
The formulas preserve the finite concatenation order of the public LP. -/

namespace Lax263307Proofs.NativeDistanceEntries

open Lax263307.DistanceProjection Lax109476.LinearProgram Lax109476.RationalEncoding

def matrixEntry {m n : ℕ} (P : Program ℚ m n) (i j : ℕ) : ℚ :=
  if hi : i < m then
    if hj : j < n then P.A ⟨i,hi⟩ ⟨j,hj⟩ else 0
  else if i < m+n then
    if j < n then if i-m=j then 1 else 0 else -1
  else if j < n then if i-(m+n)=j then -1 else 0 else -1

def boundEntry {m n : ℕ} (P : Program ℚ m n) (center : Fin n → ℚ) (i : ℕ) (hi : i < m+(n+n)) : ℚ :=
  if h : i < m then P.b ⟨i,h⟩
  else if h' : i < m+n then center ⟨i-m,by omega⟩
  else -center ⟨i-(m+n),by omega⟩

def objectiveEntry (n j : ℕ) : ℚ := if j < n then 0 else -1

theorem matrix_entry {m n : ℕ} (P : Program ℚ m n) (center : Fin n → ℚ)
    (i : Fin (m+(n+n))) (j : Fin (n+1)) :
    (distanceProgram P center).A i j=matrixEntry P i.val j.val := by
  refine Fin.addCases ?_ (Fin.addCases ?_ ?_) i
  · intro u
    refine Fin.addCases ?_ ?_ j
    · intro v
      simp [-Fin.natAdd_eq_addNat,distanceProgram,matrixEntry,u.isLt,v.isLt]
    · intro v
      have hv : v.val=0 := by have hh := v.isLt; omega
      simp [-Fin.natAdd_eq_addNat,distanceProgram,matrixEntry,u.isLt]
  · intro u
    refine Fin.addCases ?_ ?_ j
    · intro v
      have hui := u.isLt
      have hvi := v.isLt
      simp [-Fin.natAdd_eq_addNat,distanceProgram,matrixEntry,show ¬m+u.val < m by omega,
        show m+u.val < m+n by omega,hvi,Fin.ext_iff]
    · intro v
      have hv : v.val=0 := by have hh := v.isLt; omega
      have hui := u.isLt
      simp [-Fin.natAdd_eq_addNat,distanceProgram,matrixEntry,show ¬m+u.val < m by omega,
        show m+u.val < m+n by omega]
  · intro u
    refine Fin.addCases ?_ ?_ j
    · intro v
      have hui := u.isLt
      have hvi := v.isLt
      simp [-Fin.natAdd_eq_addNat,distanceProgram,matrixEntry,show ¬m+n+u.val < m by omega,
        show ¬m+n+u.val < m+n by omega,hvi,Fin.ext_iff,←Nat.add_assoc]
    · intro v
      have hv : v.val=0 := by have hh := v.isLt; omega
      have hui := u.isLt
      simp [-Fin.natAdd_eq_addNat,distanceProgram,matrixEntry,show ¬m+n+u.val < m by omega,
        show ¬m+n+u.val < m+n by omega,←Nat.add_assoc]

theorem bound_entry {m n : ℕ} (P : Program ℚ m n) (center : Fin n → ℚ)
    (i : Fin (m+(n+n))) : (distanceProgram P center).b i=boundEntry P center i.val i.isLt := by
  refine Fin.addCases ?_ (Fin.addCases ?_ ?_) i
  · intro u
    simp [-Fin.natAdd_eq_addNat,distanceProgram,boundEntry,u.isLt]
  · intro u
    have hui := u.isLt
    simp [-Fin.natAdd_eq_addNat,distanceProgram,boundEntry,show ¬m+u.val < m by omega,show m+u.val < m+n by omega]
  · intro u
    have hui := u.isLt
    simp [-Fin.natAdd_eq_addNat,distanceProgram,boundEntry,show ¬m+n+u.val < m by omega,
      show ¬m+n+u.val < m+n by omega,←Nat.add_assoc]

theorem objective_entry {m n : ℕ} (P : Program ℚ m n) (center : Fin n → ℚ)
    (j : Fin (n+1)) : (distanceProgram P center).c j=objectiveEntry n j.val := by
  refine Fin.addCases ?_ ?_ j
  · intro u
    simp [-Fin.natAdd_eq_addNat,distanceProgram,objectiveEntry,u.isLt]
  · intro u
    have hu : u.val=0 := by have hh := u.isLt; omega
    simp [-Fin.natAdd_eq_addNat,distanceProgram,objectiveEntry]

end Lax263307Proofs.NativeDistanceEntries
