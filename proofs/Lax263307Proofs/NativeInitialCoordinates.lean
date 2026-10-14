import Lax263307Proofs.NativeMatrixOrder
import Lax263307Proofs.NativeRationalTabulate

set_option maxHeartbeats 600000

namespace Lax263307Proofs.NativeInitialCoordinates

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Matrix

def values (n : ℕ) : List ℚ := List.ofFn (fun i : Fin (n*n) =>
  (1 : Matrix (Fin n) (Fin n) ℚ) (NativeBlowUp.row i) (NativeBlowUp.col i))

def read : Com := .seq (.assign "init.row" (.div (.var "fill.i") (.var "vec.n")))
  (.seq (.assign "init.col" (.sub (.var "fill.i") (.mul (.var "init.row") (.var "vec.n"))))
    (.seq (.ite (.eq (.var "init.row") (.var "init.col"))
      (.assign "coefficient.positive" (.lit 1)) (.assign "coefficient.positive" (.lit 0)))
      (.assign "coefficient.negative" (.lit 0))))

/-- Generate the identity shape's actual integer entries in flattened
matrix order. Its canonical rational encoding is produced by the table writer. -/
theorem read_spec (B n i : ℕ) (hi : i<(values n).length) (hB : n*n+n+20<B) :
    Spec B (fun σ => σ.vars "vec.n"=n ∧ σ.vars "fill.i"=i) read
      (fun _ τ => τ.vars "vec.n"=n ∧ τ.vars "coefficient.positive"<B ∧ τ.vars "coefficient.negative"<B ∧
        ((τ.vars "coefficient.positive" : ℕ) : ℚ)-τ.vars "coefficient.negative"=(values n)[i]) 18 := by
  have hin : i<n*n := by simpa only [values,List.length_ofFn] using hi
  let row := NativeBlowUp.row (⟨i,hin⟩ : Fin (n*n))
  let col := NativeBlowUp.col (⟨i,hin⟩ : Fin (n*n))
  have hiB : i<B := hin.trans (by omega)
  have hnB : n<B := by omega
  have hrB : row.val<B := row.isLt.trans hnB
  have hcolB : col.val<B := col.isLt.trans hnB
  have hmul : row.val*n ≤ i := Nat.div_mul_le_self i n
  rintro σ ⟨hn,hs⟩
  let ν := σ.setVar "init.row" row.val
  have r1 : Run B (.assign "init.row" (.div (.var "fill.i") (.var "vec.n"))) σ ν 4 := Run.assign
    (evalB_bin (op:=.div)
      (by rw [evalB_var_iff]; exact ⟨hs.symm,hs ▸ hiB⟩)
      (by rw [evalB_var_iff]; exact ⟨hn.symm,hn ▸ hnB⟩) hrB)
  let ρ := ν.setVar "init.col" col.val
  have r2 : Run B (.assign "init.col" (.sub (.var "fill.i") (.mul (.var "init.row") (.var "vec.n")))) ν ρ 6 := by
    apply Run.assign
    change (Expr.sub (.var "fill.i") (.mul (.var "init.row") (.var "vec.n"))).evalB B ν=some (i%n)
    rw [Nat.mod_eq_sub_div_mul]
    exact evalB_bin (op:=.sub)
      (by rw [evalB_var_iff]; exact ⟨((r1.frame_var "fill.i" (by decide)).trans hs).symm,
        ((r1.frame_var "fill.i" (by decide)).trans hs) ▸ hiB⟩)
      (evalB_bin (op:=.mul)
        (by rw [evalB_var_iff]; simp only [ν,vars_setVar,if_true]; exact ⟨rfl,hrB⟩)
        (by rw [evalB_var_iff]; exact ⟨((r1.frame_var "vec.n" (by decide)).trans hn).symm,
          ((r1.frame_var "vec.n" (by decide)).trans hn) ▸ hnB⟩)
        (by change row.val*n<B; omega))
      (by change i-row.val*n<B; omega)
  let pos : ℕ := if row.val=col.val then 1 else 0
  have hpB : pos<B := by dsimp [pos]; split_ifs <;> omega
  have hrρ : ρ.vars "init.row"=row.val := (r2.frame_var "init.row" (by decide)).trans (by simp [ν])
  have hcρ : ρ.vars "init.col"=col.val := by simp [ρ]
  have hc : (Cond.eq (.var "init.row") (.var "init.col")).evalB B ρ=some (decide (row.val=col.val)) := by
    have heR : (Expr.var "init.row").evalB B ρ=some row.val := by
      rw [evalB_var_iff]; exact ⟨hrρ.symm,hrρ ▸ hrB⟩
    have heC : (Expr.var "init.col").evalB B ρ=some col.val := by
      rw [evalB_var_iff]; exact ⟨hcρ.symm,hcρ ▸ hcolB⟩
    have hh := evalB_condEq heR heC
    simpa only [Bool.beq_eq_decide_eq] using hh
  let μ := ρ.setVar "coefficient.positive" pos
  have r3 : Run B (.ite (.eq (.var "init.row") (.var "init.col"))
      (.assign "coefficient.positive" (.lit 1)) (.assign "coefficient.positive" (.lit 0))) ρ μ 6 := by
    by_cases h : row.val=col.val
    · have hp : pos=1 := by simp [pos,h]
      change Run B _ ρ (ρ.setVar "coefficient.positive" pos) 6
      rw [hp]
      exact (Run.ite_true (d:=.assign "coefficient.positive" (.lit 0)) (by simpa only [h,decide_true] using hc)
        (Run.assign (evalB_lit (show 1<B by omega)))).mono (by simp [Cond.size,Expr.size])
    · have hp : pos=0 := by simp [pos,h]
      change Run B _ ρ (ρ.setVar "coefficient.positive" pos) 6
      rw [hp]
      exact (Run.ite_false (c:=.assign "coefficient.positive" (.lit 1)) (by simpa only [h,decide_false] using hc)
        (Run.assign (evalB_lit (show 0<B by omega)))).mono (by simp [Cond.size,Expr.size])
  let τ := μ.setVar "coefficient.negative" 0
  have r4 : Run B (.assign "coefficient.negative" (.lit 0)) μ τ 2 := Run.assign (evalB_lit (show 0<B by omega))
  have hentry : (values n)[i]=if row.val=col.val then (1 : ℚ) else 0 := by
    simp only [values,List.getElem_ofFn,Matrix.one_apply,Fin.ext_iff] <;> rfl
  have hpτ : τ.vars "coefficient.positive"=pos :=
    (r4.frame_var "coefficient.positive" (by decide)).trans (by rfl)
  have hnτ : τ.vars "coefficient.negative"=0 := by rfl
  refine ⟨τ,r1.seq (r2.seq (r3.seq r4)),((r1.seq (r2.seq (r3.seq r4))).frame_var "vec.n" (by decide)).trans hn,
    by rw [hpτ]; exact hpB,by rw [hnτ]; omega,?_⟩
  rw [hpτ,hnτ,hentry]
  by_cases h : row.val=col.val
  · simp only [pos,if_pos h,Nat.cast_one,Nat.cast_zero,sub_zero]
  · simp only [pos,if_neg h,Nat.cast_zero,sub_zero]

def zeroRead : Com := .seq (.assign "coefficient.positive" (.lit 0)) (.assign "coefficient.negative" (.lit 0))

theorem zero_read_spec (B n : ℕ) (hB : 0<B) :
    Spec B (fun σ => σ.vars "vec.n"=n) zeroRead
      (fun _ τ => τ.vars "vec.n"=n ∧ τ.vars "coefficient.positive"<B ∧ τ.vars "coefficient.negative"<B ∧
        ((τ.vars "coefficient.positive" : ℕ) : ℚ)-τ.vars "coefficient.negative"=0) 4 := by
  intro σ hs
  run_vcg
  all_goals simp_all [Env.setVar]

end Lax263307Proofs.NativeInitialCoordinates
