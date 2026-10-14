import Lax263307Proofs.NativeOutputRead
import Lax263307Proofs.NativeShoreMasks

namespace Lax263307Proofs.NativeShoreUpdate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open NativeShoreMasks

def bitCommand (invert : Bool) : Com := .seq NativeOutputRead.command
  (.ite (.eq (.var "output.value") (.lit 1))
    (.assign "shore.bit" (.lit (if invert then 0 else 1)))
    (.assign "shore.bit" (.lit (if invert then 1 else 0))))

theorem bit_spec (B : ℕ) (xs : List ℕ) (i : ℕ) (invert : Bool)
    (hB : xs.length+i+2<B) (hw : ∀ x∈xs,x<B) :
    Spec B (fun σ => Prefix xs "vm.output" σ ∧ σ.vars "vm.outputLength"=xs.length ∧ σ.vars "output.index"=i)
      (bitCommand invert) (fun _ τ => τ.vars "shore.bit"=
        if (if invert then xs.getD i 0≠1 else xs.getD i 0=1) then 1 else 0) 13 := by
  have hx : xs.getD i 0<B := by
    by_cases h : i<xs.length
    · simpa only [List.getD,List.getElem?_eq_getElem h,Option.getD_some] using hw _ (List.getElem_mem h)
    · simp only [List.getD,List.getElem?_eq_none (Nat.le_of_not_gt h),Option.getD_none]; omega
  have hr := NativeOutputRead.command_spec B xs i hB hw
  cases invert <;> run_vcg [hr] <;> simp_all <;> omega

def maskCommand (reg : String) : Com := .assign reg
  (.or (.var reg) (.shiftl (.var "shore.bit") (.var "shore.label")))

theorem mask_spec {r n : ℕ} (B : ℕ) (reg : String) (f : Fin r → Fin n)
    (S : Finset (Fin r)) (i : Fin r) (hB : n+2<B) (hm : 2^n<B) :
    Spec B (fun σ => σ.vars reg=partialMask f S i.val ∧
      σ.vars "shore.bit"=(if i∈S then 1 else 0) ∧ σ.vars "shore.label"=(f i).val)
      (maskCommand reg) (fun _ τ => τ.vars reg=partialMask f S (i.val+1)) 6 := by
  rintro σ ⟨hprev,hbit,hlabel⟩
  let bit : ℕ := if i∈S then 1 else 0
  have hb : bit≤1 := by dsimp [bit]; split_ifs <;> omega
  have hbB : bit<B := by omega
  have hlB : (f i).val<B := (f i).isLt.trans (by omega)
  have hpB : partialMask f S i.val<B := (bound f S i.val).trans hm
  have hnB : partialMask f S (i.val+1)<B := (bound f S (i.val+1)).trans hm
  have hsB : bit*2^(f i).val<B :=
    (by simpa only [one_mul] using Nat.mul_le_mul_right (2^(f i).val) hb : bit*2^(f i).val≤2^(f i).val).trans_lt
      ((Nat.pow_lt_pow_right (by decide : 1<2) (f i).isLt).trans hm)
  have he := evalB_bin (op:=.or)
    (by rw [evalB_var_iff]; exact ⟨hprev.symm,hprev ▸ hpB⟩)
    (evalB_bin (op:=.shiftl)
      (by rw [evalB_var_iff]; exact ⟨hbit.symm,hbit ▸ hbB⟩)
      (by rw [evalB_var_iff]; exact ⟨hlabel.symm,hlabel ▸ hlB⟩) hsB)
    (by change Nat.lor (partialMask f S i.val) (bit*2^(f i).val)<B; rw [step]; exact hnB)
  have he' : (Expr.or (.var reg) (.shiftl (.var "shore.bit") (.var "shore.label"))).evalB B σ=
      some (partialMask f S (i.val+1)) := by
    simpa only [Bop.apply_or,Bop.apply_shiftl,bit,step] using he
  exact ⟨σ.setVar reg (partialMask f S (i.val+1)),Run.assign he',by simp⟩

end Lax263307Proofs.NativeShoreUpdate
