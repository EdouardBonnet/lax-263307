import Lax263307Proofs.NativeRecursionDepth
import Lax263307Proofs.NativeSignedArithmetic
import Lax263307.RecursiveAlgorithm

namespace Lax263307Proofs.NativeRootAccuracy

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 RecursionDepth

theorem ceil_div (n d : ℕ) (hn : 0<n) (hd : 0<d) :
    ⌈((n : ℚ)/d)⌉₊=(n+d-1)/d := by
  let k := (n+d-1)/d
  have hsum : n+d-1+1=n+d := by omega
  have hk : 1≤k := (Nat.le_div_iff_mul_le hd).mpr (by simp; omega)
  have hlo : k*d≤n+d-1 := Nat.div_mul_le_self (n+d-1) d
  have hhi : n+d-1<(k+1)*d := (Nat.div_lt_iff_lt_mul hd).mp (by change k<k+1; omega)
  have hkstep : k=k-1+1 := by omega
  have hu : n≤k*d := by nlinarith only [hhi,hsum]
  have hl : (k-1)*d<n := by nlinarith only [hlo,hsum,hkstep]
  have hdq : 0<(d : ℚ) := by exact_mod_cast hd
  apply (Nat.ceil_eq_iff (by omega : k≠0)).mpr
  constructor
  · apply (lt_div_iff₀ hdq).mpr
    exact_mod_cast hl
  · apply (div_le_iff₀ hdq).mpr
    exact_mod_cast hu

theorem inverse_half (ε : ℚ) (hε : 0<ε) :
    (ε/2)⁻¹=((2*ε.den : ℕ) : ℚ)/(ε.num.natAbs : ℚ) := by
  have hnum : (ε.num.natAbs : ℚ)=(ε.num : ℚ) := by
    have he : (ε.num.natAbs : ℤ)=ε.num := Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hε.le)
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) he
  have hvalue : (ε.num.natAbs : ℚ)/(ε.den : ℚ)=ε := by rw [hnum,ε.num_div_den]
  have he : ε⁻¹=(ε.den : ℚ)/(ε.num.natAbs : ℚ) := by
    calc
      _ = ((ε.num.natAbs : ℚ)/(ε.den : ℚ))⁻¹ := congrArg Inv.inv hvalue.symm
      _ = _ := inv_div _ _
  calc
    _ = (2 : ℚ)*ε⁻¹ := by rw [inv_div,div_eq_mul_inv]
    _ = _ := by rw [he]; push_cast; ring

def finish : Com := .seq (.assign "algorithm.E"
  (.div (.sub (.add (.mul (.lit 2) (.var "accuracy.d")) (.var "accuracy.n")) (.lit 1)) (.var "accuracy.n")))
  (.seq (.assign "node.D" (.mul (.mul (.lit 4) (.add (.var "depth.count") (.lit 1))) (.var "algorithm.E")))
    (.assign "recursion.fuel" (.var "depth.count")))

def command : Com := .seq NativeRecursionDepth.command finish

theorem finish_spec (B M n : ℕ) (ε : ℚ) (hε : 0<ε) (hM : NativeSignedArithmetic.Bounded M ε)
    (hB : 3*M+8*(depth n+1)*M+2*n+depth n+40<B) :
    Spec B (fun σ => σ.vars "accuracy.n"=ε.num.natAbs ∧ σ.vars "accuracy.d"=ε.den ∧
      σ.vars "depth.count"=depth n) finish
      (fun _ τ => τ.vars "algorithm.E"=⌈(ε/2)⁻¹⌉₊ ∧
        τ.vars "node.D"=RecursiveAlgorithm.accuracyDenominator n (ε/2) ∧
        τ.vars "recursion.fuel"=depth n) 20 := by
  have hnum : 0<ε.num.natAbs := by
    by_contra hh
    have hz : ε.num=0 := Int.natAbs_eq_zero.mp (by omega)
    have he : ε=0 := by rw [←ε.num_div_den,hz]; simp
    linarith
  have hc : (2*ε.den+ε.num.natAbs-1)/ε.num.natAbs=⌈(ε/2)⁻¹⌉₊ := by
    rw [inverse_half ε hε]
    exact (ceil_div (2*ε.den) ε.num.natAbs (by have hh:=ε.den_pos; omega) hnum).symm
  have he : ⌈(ε/2)⁻¹⌉₊≤2*M := by
    rw [inverse_half ε hε]
    apply (Nat.ceil_le.mpr (div_le_self (by positivity) (by exact_mod_cast (show 1≤ε.num.natAbs by omega)))).trans
    exact Nat.mul_le_mul_left 2 hM.2
  have hdenBudget : 4*(depth n+1)*⌈(ε/2)⁻¹⌉₊≤8*(depth n+1)*M := by
    have hh := Nat.mul_le_mul_left (4*(depth n+1)) he
    nlinarith only [hh]
  have htop : 2*ε.den+ε.num.natAbs-1≤3*M := by have h1:=hM.1; have h2:=hM.2; omega
  have hMpos : 1≤M := ε.den_pos.trans_le hM.2
  have hprod : 4*(depth n+1)≤8*(depth n+1)*M := by
    have hh := Nat.mul_le_mul_left (4*(depth n+1)) hMpos
    nlinarith only [hh]
  intro σ hs
  run_vcg
  all_goals simp_all [Env.setVar,RecursiveAlgorithm.accuracyDenominator]
  all_goals nlinarith [hM.1,hM.2]

/-- Set the recursive solver's exact depth and half-accuracy budgets
from the stored original accuracy, matching the weighted algorithm. -/
theorem command_spec (B M n : ℕ) (ε : ℚ) (hε : 0<ε) (hM : NativeSignedArithmetic.Bounded M ε)
    (hB : 3*M+8*(depth n+1)*M+2*n+depth n+40<B) :
    Spec B (fun σ => σ.vars "graph.n"=n ∧ σ.vars "accuracy.n"=ε.num.natAbs ∧ σ.vars "accuracy.d"=ε.den)
      command (fun _ τ => τ.vars "graph.n"=n ∧ τ.vars "algorithm.E"=⌈(ε/2)⁻¹⌉₊ ∧
        τ.vars "node.D"=RecursiveAlgorithm.accuracyDenominator n (ε/2) ∧ τ.vars "recursion.fuel"=depth n)
      (14*depth n+28) := by
  rintro σ ⟨hn,hnε,hdε⟩
  obtain ⟨ν,r1,p1⟩ := NativeRecursionDepth.command_spec B n (by omega) σ hn
  obtain ⟨τ,r2,p2⟩ := finish_spec B M n ε hε hM hB ν
    ⟨(r1.frame_var "accuracy.n" (by decide)).trans hnε,(r1.frame_var "accuracy.d" (by decide)).trans hdε,p1.2⟩
  exact ⟨τ,(r1.seq r2).mono (by omega),(r2.frame_var "graph.n" (by decide)).trans p1.1,p2⟩

end Lax263307Proofs.NativeRootAccuracy
