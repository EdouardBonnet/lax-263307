import Lax263307Proofs.NativeNaturalPower
import Lax455465Proofs.RamBitSize
import Lax263307.HeavyRationalConditioning

namespace Lax263307Proofs.NativeConditioningFloor

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

def base (n p : ℕ) : ℕ := 2*n*p*(Nat.log2 n+1)

theorem size_log (n : ℕ) (hn : 0<n) : n.size=Nat.log2 n+1 := by
  have hlo : 2^(Nat.log2 n)≤n := by
    rw [Nat.log2_eq_log_two]
    exact Nat.pow_log_le_self 2 (by omega)
  have hhi : n<2^(Nat.log2 n+1) := by
    rw [Nat.log2_eq_log_two]
    exact Nat.lt_pow_succ_log_self (by decide) n
  have hslo := Nat.lt_size.mpr hlo
  have hshi := Nat.size_le.mpr hhi
  omega

def preparePower : Com := .seq
  (.assign "power.base" (.mul (.mul (.mul (.lit 2) (.var "graph.n")) (.var "conditioning.p")) (.var "size.count")))
  (.assign "power.exponent" (.var "moment.r"))

def command : Com := .seq (.assign "size.value" (.var "graph.n"))
  (.seq RamBitSize.word (.seq preparePower
    (.seq NativeNaturalPower.command (.assign "conditioning.floorDen" (.var "power.value")))))

/-- Compute the denominator of the heavy-conditioning moment floor.
The logarithm is obtained by actual integer halving and the exponent
by an exact multiplication loop. -/
theorem command_spec (B n p r : ℕ) (hn : 0<n) (hp : 0<p)
    (hB : base n p+base n p^r+n+p+r+10<B) :
    Spec B (fun σ => σ.vars "graph.n"=n ∧ σ.vars "conditioning.p"=p ∧ σ.vars "moment.r"=r) command
      (fun _ τ => τ.vars "conditioning.floorDen"=base n p^r) (12*n.size+12*r+28) := by
  have hb : 1≤base n p := by change 0<base n p; dsimp [base]; positivity
  have hlog : 1≤n.size := by rw [size_log n hn]; omega
  have hsize : n.size≤n := Nat.size_le.mpr Nat.lt_two_pow_self
  have hnp : 2*n*p≤base n p := by
    dsimp [base]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hn2 : 2*n≤base n p := (Nat.le_mul_of_pos_right _ hp).trans hnp
  have hprep : Spec B (fun σ => σ.vars "graph.n"=n ∧ σ.vars "conditioning.p"=p ∧
      σ.vars "moment.r"=r ∧ σ.vars "size.count"=n.size) preparePower
      (fun _ τ => NativeNaturalPower.Context (base n p) r τ) 10 := by
    have hval : 2*n*p*n.size=base n p := by rw [size_log n hn]; rfl
    run_vcg
    all_goals simp_all [NativeNaturalPower.Context]
    all_goals omega
  rintro σ ⟨hN,hP,hR⟩
  let ν := σ.setVar "size.value" n
  have r1 : Run B (.assign "size.value" (.var "graph.n")) σ ν 2 :=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hN.symm,hN ▸ (by omega : n<B)⟩)
  obtain ⟨μ,r2,p2⟩ := RamBitSize.word_spec B n (by omega) (by omega) ν (by simp [ν])
  have r12 := r1.seq r2
  obtain ⟨ξ,r3,p3⟩ := hprep μ ⟨(r12.frame_var "graph.n" (by decide)).trans hN,
    (r12.frame_var "conditioning.p" (by decide)).trans hP,(r12.frame_var "moment.r" (by decide)).trans hR,p2.2⟩
  obtain ⟨υ,r4,p4⟩ := NativeNaturalPower.command_spec B (base n p) r hb (by omega) ξ p3
  let τ := υ.setVar "conditioning.floorDen" (base n p^r)
  have r5 : Run B (.assign "conditioning.floorDen" (.var "power.value")) υ τ 2 :=
    Run.assign (by rw [evalB_var_iff]; exact ⟨p4.2.symm,p4.2 ▸ (by omega : base n p^r<B)⟩)
  exact ⟨τ,(r1.seq (r2.seq (r3.seq (r4.seq r5)))).mono (by omega),by simp [τ]⟩

theorem floor_value (n p r : ℕ) : Lax263307.HeavyRationalConditioning.rationalFloor n p^r=
    1/(base n p^r : ℕ) := by
  simp only [Lax263307.HeavyRationalConditioning.rationalFloor,base,Nat.cast_mul,Nat.cast_ofNat,
    Nat.cast_add,Nat.cast_one,Nat.cast_pow,one_div_pow]

end Lax263307Proofs.NativeConditioningFloor
