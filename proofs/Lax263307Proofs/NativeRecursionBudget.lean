import Lax263307Proofs.ParameterResources
import Lax263307Proofs.RecursionDepth

namespace Lax263307Proofs.NativeRecursionBudget

open Lax263307 AlgorithmParameters

def work (localCost branches : ℕ) : ℕ → ℕ
  | 0 => localCost
  | fuel+1 => localCost+branches*work localCost branches fuel

theorem work_le_pow (localCost branches R fuel : ℕ) (hl : localCost≤R) (hb : branches≤R) :
    work localCost branches fuel≤(R+1)^(fuel+1) := by
  induction fuel with
  | zero => simpa only [work,Nat.zero_add,pow_one] using hl.trans (Nat.le_succ R)
  | succ fuel ih =>
    have hp : R≤(R+1)^(fuel+1) := (Nat.le_succ R).trans (le_self_pow (by omega) (by omega))
    calc
      work localCost branches (fuel+1)≤R+R*(R+1)^(fuel+1) :=
        Nat.add_le_add hl (Nat.mul_le_mul hb ih)
      _≤(R+1)^(fuel+1)*(R+1) := by nlinarith only [hp]
      _=(R+1)^((fuel+1)+1) := (pow_succ _ _).symm

/-- Polynomial local work and branching, repeated through logarithmic
depth, still fit a quasipolynomial envelope. -/
theorem amplify (C d n D localCost branches : ℕ) (hD : 0<D)
    (hl : localCost≤2^(C*(D*logarithm n)^d))
    (hb : branches≤2^(C*(D*logarithm n)^d)) :
    work localCost branches (RecursionDepth.depth n)≤
      2^(3*(C+1)*(D*logarithm n)^(d+1)) := by
  let X := D*logarithm n
  have hlog : 1≤logarithm n := by dsimp [logarithm]; omega
  have hX : 1≤X := by dsimp [X]; nlinarith only [hlog,hD]
  have hLX : logarithm n≤X := Nat.le_mul_of_pos_left _ hD
  have hd : RecursionDepth.depth n+1≤3*X := by
    have hdepth := RecursionDepth.logarithmic_bound n
    have hmono := ParameterResources.logarithm_mono n
    omega
  have hxpow : 1≤X^d := Nat.one_le_pow _ _ hX
  have he : C*X^d+1≤(C+1)*X^d := by nlinarith only [hxpow]
  have hp : 2^(C*X^d)+1≤2^(C*X^d+1) := by
    have hpos : 1≤2^(C*X^d) := Nat.one_le_pow _ _ (by decide)
    rw [pow_succ]
    omega
  calc
    work localCost branches (RecursionDepth.depth n)≤(2^(C*X^d)+1)^(RecursionDepth.depth n+1) :=
      work_le_pow _ _ _ _ hl hb
    _≤(2^(C*X^d+1))^(RecursionDepth.depth n+1) := Nat.pow_le_pow_left hp _
    _=2^((C*X^d+1)*(RecursionDepth.depth n+1)) := (pow_mul _ _ _).symm
    _≤2^(((C+1)*X^d)*(3*X)) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul he hd)
    _=2^(3*(C+1)*(D*logarithm n)^(d+1)) := by rw [pow_succ]; dsimp only [X]; congr 1; ring

/-- Any fixed polynomial degree of the checked parameter resource has
the required global growth rate after recursive amplification. -/
theorem resource_amplification (a K B e : ℕ) (hK : 0<K) :
    ∃ C d : ℕ,0<C ∧ 0<d ∧ ∀ n D : ℕ,0<n → 0<D →
      let R := (Lax263307.ParameterResources.resource a K B n D+1)^e
      work R R (RecursionDepth.depth n)≤2^(C*(D*logarithm n)^d) := by
  obtain ⟨C,d,hC,hd,hresource⟩ := ParameterResources.resource_bound a K B hK
  refine ⟨3*(e*(C+1)+1),d+1,by positivity,by omega,?_⟩
  intro n D hn hD
  dsimp only
  let X := D*logarithm n
  have hX : 1≤X := by
    have hx : 0<X := by dsimp [X,logarithm]; positivity
    omega
  have hxpow : 1≤X^d := Nat.one_le_pow _ _ hX
  have hp : 2^(C*X^d)+1≤2^(C*X^d+1) := by
    have hpos : 1≤2^(C*X^d) := Nat.one_le_pow _ _ (by decide)
    rw [pow_succ]; omega
  have hlocal : (Lax263307.ParameterResources.resource a K B n D+1)^e≤2^((e*(C+1))*X^d) := by
    calc
      _≤(2^(C*X^d)+1)^e := Nat.pow_le_pow_left (Nat.add_le_add_right (hresource n D hn hD) 1) _
      _≤(2^(C*X^d+1))^e := Nat.pow_le_pow_left hp _
      _=2^((C*X^d+1)*e) := (pow_mul _ _ _).symm
      _≤2^((e*(C+1))*X^d) := Nat.pow_le_pow_right (by decide) (by nlinarith only [hxpow])
  exact amplify (e*(C+1)) d n D _ _ hD hlocal hlocal

end Lax263307Proofs.NativeRecursionBudget
