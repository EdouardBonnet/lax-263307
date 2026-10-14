import Lax263307Proofs.NativeRationalBounds
import Lax263307.RationalCutBuffer
import Mathlib.Data.List.OfFn

namespace Lax263307Proofs.NativeDenominatorData

open Lax263307.RationalCutBuffer

def product (qs : List ℚ) : ℕ := (qs.map Rat.den).prod

def partialProduct {n : ℕ} (a : Fin n → ℚ) (i : ℕ) : ℕ := product ((List.ofFn a).take i)

theorem product_positive (qs : List ℚ) : 0<product qs := by
  induction qs with
  | nil => simp [product]
  | cons q qs ih => exact Nat.mul_pos q.den_pos ih

theorem full_product {n : ℕ} (a : Fin n → ℚ) : partialProduct a n=denominator a := by
  have ht : (List.ofFn a).take n=List.ofFn a := by
    simpa only [List.length_ofFn] using (List.take_length : (List.ofFn a).take (List.ofFn a).length=List.ofFn a)
  rw [partialProduct,ht]
  simp only [product,denominator,List.map_ofFn,List.prod_ofFn,Function.comp_apply]

theorem partial_le {n : ℕ} (a : Fin n → ℚ) (i : ℕ) : partialProduct a i≤denominator a := by
  have hsplit : denominator a=partialProduct a i*product ((List.ofFn a).drop i) := by
    have ht : (List.ofFn a).take n=List.ofFn a := by
      simpa only [List.length_ofFn] using (List.take_length : (List.ofFn a).take (List.ofFn a).length=List.ofFn a)
    have hf : product (List.ofFn a)=denominator a := by
      simpa only [partialProduct,ht] using full_product a
    rw [←hf]
    conv_lhs => rw [←List.take_append_drop i (List.ofFn a)]
    simp only [partialProduct,product,List.map_append,List.prod_append]
  have hp := product_positive ((List.ofFn a).drop i)
  rw [hsplit]
  nlinarith

theorem partial_step {n : ℕ} (a : Fin n → ℚ) (i : Fin n) :
    partialProduct a (i.val+1)=partialProduct a i.val*(a i).den := by
  unfold partialProduct
  rw [List.take_succ_eq_append_getElem (by simpa using i.isLt)]
  simp only [product,List.map_append,List.prod_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    Nat.mul_one,List.getElem_ofFn]

theorem denominator_positive' {n : ℕ} (a : Fin n → ℚ) : 0<denominator a := by
  rw [←full_product]
  exact product_positive _

end Lax263307Proofs.NativeDenominatorData
