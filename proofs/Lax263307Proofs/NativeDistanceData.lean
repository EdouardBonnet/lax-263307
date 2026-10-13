import Lax263307Proofs.NativeDistanceCoefficient
import Lax455465Proofs.RamVectorEncoding

namespace Lax263307Proofs.NativeDistanceData

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax263307.DistanceProjection
open NativeDistanceEntries

abbrev rows (m n : ℕ) : ℕ := m+(n+n)
abbrev columns (n : ℕ) : ℕ := n+1

def wordLength (m n : ℕ) : ℕ := 2+3*(rows m n*columns n+rows m n+columns n)
def shapeSize (m n : ℕ) : ℕ := 3*(m*n)+5*m+5*n+wordLength m n+30

structure Data {m n : ℕ} (P : Program ℚ m n) (x : Fin n → ℚ) (σ : Env) : Prop where
  source : Prefix (encodeProgram P) "lp.input" σ
  center : Prefix (encodeVector x) "projection.center" σ
  oldRows : σ.vars "projection.m"=m
  oldColumns : σ.vars "projection.n"=n
  rowCount : σ.vars "lp.rows"=rows m n
  columnCount : σ.vars "lp.columns"=columns n
  matrixLength : σ.vars "projection.matrixLength"=rows m n*columns n

def fields : List String := ["projection.m","projection.n","lp.rows","lp.columns","projection.matrixLength"]
def arrays : List String := ["lp.input","projection.center"]

theorem frame {m n B K : ℕ} (P : Program ℚ m n) (x : Fin n → ℚ) {σ τ : Env} {c : Com}
    (rr : Run B c σ τ K) (h : Data P x σ) (hv : ∀ a ∈ fields,a∉c.wvars) (ha : ∀ a ∈ arrays,a∉c.warrs) :
    Data P x τ := by
  constructor
  · simpa only [Prefix,rr.frame_arr "lp.input" (ha _ (by decide))] using h.source
  · simpa only [Prefix,rr.frame_arr "projection.center" (ha _ (by decide))] using h.center
  · exact (rr.frame_var "projection.m" (hv _ (by decide))).trans h.oldRows
  · exact (rr.frame_var "projection.n" (hv _ (by decide))).trans h.oldColumns
  · exact (rr.frame_var "lp.rows" (hv _ (by decide))).trans h.rowCount
  · exact (rr.frame_var "lp.columns" (hv _ (by decide))).trans h.columnCount
  · exact (rr.frame_var "projection.matrixLength" (hv _ (by decide))).trans h.matrixLength

theorem set_entry {m n : ℕ} (P : Program ℚ m n) (x : Fin n → ℚ) (σ : Env) (k : ℕ) (h : Data P x σ) :
    Data P x (σ.setVar "projection.entry" k) := by
  constructor
  · exact h.source
  · exact h.center
  · exact h.oldRows
  · exact h.oldColumns
  · exact h.rowCount
  · exact h.columnCount
  · exact h.matrixLength

def Height (B : ℕ) (q : ℚ) : Prop := q.num.natAbs < B ∧ q.den < B

structure Bounded {m n : ℕ} (B : ℕ) (P : Program ℚ m n) (x : Fin n → ℚ) : Prop where
  one : 1 < B
  matrix : ∀ i j,Height B (P.A i j)
  bound : ∀ i,Height B (P.b i)
  center : ∀ i,Height B (x i)

theorem matrix_height {m n : ℕ} (B : ℕ) (P : Program ℚ m n) (x : Fin n → ℚ) (hb : Bounded B P x)
    (i : Fin (rows m n)) (j : Fin (columns n)) : Height B ((distanceProgram P x).A i j) := by
  rw [matrix_entry]
  unfold matrixEntry
  split_ifs
  all_goals first | exact hb.matrix _ _ | simpa [Height] using hb.one | simp only [Height,Rat.num_zero,Rat.den_zero,Int.natAbs_zero]; exact ⟨by have hh := hb.one; omega,hb.one⟩

theorem bound_height {m n : ℕ} (B : ℕ) (P : Program ℚ m n) (x : Fin n → ℚ) (hb : Bounded B P x)
    (i : Fin (rows m n)) : Height B ((distanceProgram P x).b i) := by
  rw [bound_entry]
  unfold boundEntry
  split_ifs
  · exact hb.bound _
  · exact hb.center _
  · simpa only [Height,Rat.neg_num,Int.natAbs_neg,Rat.neg_den] using hb.center _

theorem objective_height {m n : ℕ} (B : ℕ) (P : Program ℚ m n) (x : Fin n → ℚ) (hb : Bounded B P x)
    (j : Fin (columns n)) : Height B ((distanceProgram P x).c j) := by
  rw [objective_entry]
  unfold objectiveEntry
  split_ifs
  · simp only [Height,Rat.num_zero,Rat.den_zero,Int.natAbs_zero]
    exact ⟨by have hh := hb.one; omega,hb.one⟩
  · simpa [Height] using hb.one

end Lax263307Proofs.NativeDistanceData
