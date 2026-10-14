import Lax263307.ComputedRounding
import Lax263307Proofs.NativeSignedArithmetic

set_option maxHeartbeats 600000

namespace Lax263307Proofs.NativeComponentTarget

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamRational

def numerator (D : ℕ) (q : ℚ) : ℕ := (D-1)*q.num.natAbs
def denominator (D : ℕ) (q : ℚ) : ℕ := D*q.den
def left (n D : ℕ) (q : ℚ) : ℕ := 4*n*D*q.num.natAbs
def right (k : ℕ) (q : ℚ) : ℕ := k*q.den
def value (D : ℕ) (q : ℚ) : ℕ := numerator D q/denominator D q+1

def resource (n D k : ℕ) (q : ℚ) : ℕ :=
  n+D+k+q.num.natAbs+q.den+4*n+4*n*D+left n D q+right k q+
    2*numerator D q+denominator D q+20

theorem nonnegative_encoding (q : ℚ) (hq : 0≤q) :
    (q.num.natAbs : ℚ)/(q.den : ℚ)=q := by
  have he : (q.num.natAbs : ℤ)=q.num := Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hq)
  have hc : (q.num.natAbs : ℚ)=(q.num : ℚ) := by
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) he
  rw [hc,q.num_div_den]

theorem target_eq (D : ℕ) (q : ℚ) (hD : 0<D) (hq : 0≤q) :
    Lax263307.ComputedRounding.target (1/(D : ℚ)) q=value D q := by
  have hDc : (D : ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hD)
  have hqc : (q.den : ℚ)≠0 := by exact_mod_cast q.den_ne_zero
  have he : (1-1/(D : ℚ))*q=(numerator D q : ℚ)/(denominator D q : ℚ) := by
    calc
      _=(1-1/(D : ℚ))*((q.num.natAbs : ℚ)/(q.den : ℚ)) :=
        congrArg (fun z : ℚ => (1-1/(D : ℚ))*z) (nonnegative_encoding q hq).symm
      _=_ := by
        simp only [numerator,denominator,Nat.cast_mul,Nat.cast_sub (show 1≤D by omega),Nat.cast_one]
        field_simp [hDc,hqc]
        <;> ring
  unfold Lax263307.ComputedRounding.target value
  rw [he,Rat.natFloor_natCast_div_natCast]

theorem heavy_iff (n D k : ℕ) (q : ℚ) (hn : 0<n) (hD : 0<D) (hq : 0≤q) :
    right k q<left n D q ↔ (1/(D : ℚ))*k/(4*(n : ℚ))<q := by
  have hDc : (D : ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hD)
  have hnc : (n : ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hqc : 0<(q.den : ℚ) := by exact_mod_cast q.den_pos
  have hprod : 0<4*(n : ℚ)*D := by positivity
  have he : (1/(D : ℚ))*k/(4*(n : ℚ))=(k : ℚ)/(4*n*D) := by field_simp [hDc,hnc] <;> ring
  rw [he]
  have hc : (k*q.den : ℚ)<(q.num.natAbs : ℚ)*(4*n*D) ↔ k*q.den<4*n*D*q.num.natAbs := by
    norm_cast <;> ring_nf
  have hcross : (k : ℚ)/(4*n*D)<(q.num.natAbs : ℚ)/(q.den : ℚ) ↔ right k q<left n D q := by
    rw [div_lt_div_iff₀ hprod hqc]
    exact hc
  have hencode : (k : ℚ)/(4*n*D)<q ↔ (k : ℚ)/(4*n*D)<(q.num.natAbs : ℚ)/(q.den : ℚ) := by
    rw [nonnegative_encoding q hq]
  exact (hencode.trans hcross).symm

def products : Com := .seq (.assign "component.numerator" (.mul (.sub (.var "algorithm.D") (.lit 1)) (.var "rat.n")))
  (.seq (.assign "component.denominator" (.mul (.var "algorithm.D") (.var "rat.d")))
    (.seq (.assign "component.left" (.mul (.mul (.mul (.lit 4) (.var "graph.n")) (.var "algorithm.D")) (.var "rat.n")))
      (.assign "component.right" (.mul (.var "conditioning.k") (.var "rat.d")))))

def finish : Com := .seq (.assign "component.target" (.add (.div (.var "component.numerator") (.var "component.denominator")) (.lit 1)))
  (.ite (.lt (.var "component.right") (.var "component.left"))
    (.assign "component.active" (.lit 1)) (.assign "component.active" (.lit 0)))

def command : Com := .seq products finish

/-- Compute the exact rounded target and heavy/light decision from a
component's canonical rational cost by bounded integer operations. -/
theorem command_spec (B n D k : ℕ) (q : ℚ) (hn : 0<n) (hD : 0<D) (hq : 0≤q)
    (hB : resource n D k q<B) :
    Spec B (fun σ => σ.vars "graph.n"=n ∧ σ.vars "algorithm.D"=D ∧
      σ.vars "conditioning.k"=k ∧ FractionOutput q σ) command
      (fun _ τ => τ.vars "component.target"=Lax263307.ComputedRounding.target (1/(D : ℚ)) q ∧
        τ.vars "component.active"=if (1/(D : ℚ))*k/(4*(n : ℚ))<q then 1 else 0) 34 := by
  have hg := hB
  dsimp [resource,numerator,denominator,left,right] at hg
  have hnB : numerator D q+2<B := by dsimp [numerator]; omega
  have hdB : denominator D q<B := by dsimp [denominator]; omega
  have hlB : left n D q<B := by dsimp [left]; omega
  have hrB : right k q<B := by dsimp [right]; omega
  have hp : Spec B (fun σ => σ.vars "graph.n"=n ∧ σ.vars "algorithm.D"=D ∧
      σ.vars "conditioning.k"=k ∧ FractionOutput q σ) products
      (fun _ τ => τ.vars "component.numerator"=numerator D q ∧
        τ.vars "component.denominator"=denominator D q ∧ τ.vars "component.left"=left n D q ∧
        τ.vars "component.right"=right k q) 22 := by
    run_vcg
    all_goals simp_all [FractionOutput,numerator,denominator,left,right]
    all_goals omega
  have htB : value D q<B := by
    have hh := Nat.div_le_self (numerator D q) (denominator D q)
    dsimp only [value]
    omega
  rintro σ hs
  obtain ⟨ν,r1,p1⟩ := hp σ hs
  let μ := ν.setVar "component.target" (value D q)
  have r2 : Run B (.assign "component.target" (.add (.div (.var "component.numerator") (.var "component.denominator")) (.lit 1))) ν μ 6 := Run.assign
    (evalB_bin (op:=.add)
      (evalB_bin (op:=.div)
        (by rw [evalB_var_iff]; exact ⟨p1.1.symm,p1.1 ▸ (by omega : numerator D q<B)⟩)
        (by rw [evalB_var_iff]; exact ⟨p1.2.1.symm,p1.2.1 ▸ (by omega : denominator D q<B)⟩)
        (by change numerator D q/denominator D q<B; have hh := Nat.div_le_self (numerator D q) (denominator D q); omega))
      (evalB_lit (show 1<B by omega)) htB)
  have hleft := (r2.frame_var "component.left" (by decide)).trans p1.2.2.1
  have hright := (r2.frame_var "component.right" (by decide)).trans p1.2.2.2
  have hc : (Cond.lt (.var "component.right") (.var "component.left")).evalB B μ=
      some (decide (right k q<left n D q)) := evalB_condLt
    (by rw [evalB_var_iff]; exact ⟨hright.symm,hright ▸ (by omega : right k q<B)⟩)
    (by rw [evalB_var_iff]; exact ⟨hleft.symm,hleft ▸ (by omega : left n D q<B)⟩)
  by_cases h : right k q<left n D q
  · let τ := μ.setVar "component.active" 1
    have r3 : Run B (.assign "component.active" (.lit 1)) μ τ 2 := Run.assign (evalB_lit (show 1<B by omega))
    have rb := Run.ite_true (d:=.assign "component.active" (.lit 0)) (by simpa only [h,decide_true] using hc) r3
    refine ⟨τ,(r1.seq (r2.seq rb)).mono (by simp [Cond.size,Expr.size]),
      by simpa only [τ,μ,vars_setVar,String.reduceEq,if_false,if_true] using (target_eq D q hD hq).symm,
      ?_⟩
    rw [if_pos ((heavy_iff n D k q hn hD hq).mp h)]
    simp only [τ,vars_setVar,if_true]
  · let τ := μ.setVar "component.active" 0
    have r3 : Run B (.assign "component.active" (.lit 0)) μ τ 2 := Run.assign (evalB_lit (show 0<B by omega))
    have rb := Run.ite_false (c:=.assign "component.active" (.lit 1)) (by simpa only [h,decide_false] using hc) r3
    refine ⟨τ,(r1.seq (r2.seq rb)).mono (by simp [Cond.size,Expr.size]),
      by simpa only [τ,μ,vars_setVar,String.reduceEq,if_false,if_true] using (target_eq D q hD hq).symm,
      ?_⟩
    rw [if_neg (mt (heavy_iff n D k q hn hD hq).mpr h)]
    simp only [τ,vars_setVar,if_true]

end Lax263307Proofs.NativeComponentTarget
