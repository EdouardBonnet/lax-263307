import Lax263307Proofs.NativeBlowUp

namespace Lax263307Proofs.NativeMatrixOrder

theorem row_pair (n : ℕ) (u v : Fin n) :
    NativeBlowUp.row ⟨u.val*n+v.val,by nlinarith [u.isLt,v.isLt]⟩=u := by
  have hn : 0<n := by have hu := u.isLt; omega
  apply Fin.ext
  change (u.val*n+v.val)/n=u.val
  rw [Nat.add_comm,Nat.add_mul_div_right _ _ hn,Nat.div_eq_of_lt v.isLt,Nat.zero_add]

theorem col_pair (n : ℕ) (u v : Fin n) :
    NativeBlowUp.col ⟨u.val*n+v.val,by nlinarith [u.isLt,v.isLt]⟩=v := by
  apply Fin.ext
  simp [NativeBlowUp.col,Nat.mod_eq_of_lt v.isLt]

theorem flatten {α : Type*} (n : ℕ) (f : Fin n → Fin n → α) :
    List.ofFn (fun i : Fin (n*n) => f (NativeBlowUp.row i) (NativeBlowUp.col i))=
      (List.ofFn fun u => List.ofFn (f u)).flatten := by
  rw [List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext u
  apply congrArg List.ofFn
  funext v
  simp only [row_pair,col_pair]

end Lax263307Proofs.NativeMatrixOrder
