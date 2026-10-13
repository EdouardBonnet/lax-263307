import Lax263307Proofs.NativeRationalRead

namespace Lax263307Proofs.NativeDistanceUnits

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamRational Lax455465Proofs.RamFractionPrimitives

def unit (negative : Bool) : Com := if negative then negativeOne else one

def unitValue (negative : Bool) : ℚ := if negative then -1 else 1

theorem unit_spec (B : ℕ) (negative : Bool) (h1 : 1 < B) :
    Spec B (fun _ => True) (unit negative) (fun _ τ => FractionOutput (unitValue negative) τ) 6 := by
  cases negative
  · exact one_spec B h1
  · exact negativeOne_spec B h1

def matching (negative : Bool) : Com := .ite (.eq (.var "projection.local") (.var "projection.j")) (unit negative) zero

def matchingValue (negative : Bool) (a j : ℕ) : ℚ := if a=j then unitValue negative else 0

theorem matching_spec (B : ℕ) (negative : Bool) (a j : ℕ) (hB : a+j+3 < B) :
    Spec B (fun σ => σ.vars "projection.local"=a ∧ σ.vars "projection.j"=j) (matching negative)
      (fun _ τ => FractionOutput (matchingValue negative a j) τ) 10 := by
  have hu := unit_spec B negative (by omega)
  have hz := zero_spec B (by omega)
  by_cases h : a=j
  · run_vcg [hu,hz]
    all_goals simp_all [matchingValue]
  · run_vcg [hu,hz]
    all_goals simp_all [matchingValue]

def extended (negative : Bool) : Com := .ite (.lt (.var "projection.j") (.var "projection.n")) (matching negative) negativeOne

def extendedValue (negative : Bool) (n a j : ℕ) : ℚ := if j < n then matchingValue negative a j else -1

theorem extended_spec (B : ℕ) (negative : Bool) (n a j : ℕ) (hB : n+a+j+3 < B) :
    Spec B (fun σ => σ.vars "projection.n"=n ∧ σ.vars "projection.local"=a ∧ σ.vars "projection.j"=j)
      (extended negative) (fun _ τ => FractionOutput (extendedValue negative n a j) τ) 14 := by
  have hmatch := matching_spec B negative a j (by omega)
  have hneg := negativeOne_spec B (by omega)
  by_cases h : j < n
  · run_vcg [hmatch,hneg]
    all_goals simp_all [extendedValue]
  · have he : extendedValue negative n a j = -1 := by simp [extendedValue,h]
    run_vcg [hmatch,hneg]
    all_goals simp_all only

end Lax263307Proofs.NativeDistanceUnits
