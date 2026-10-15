import Lax263307Proofs.NativeRecursionBudget

namespace Lax263307Proofs.NativeRootResource

open Lax263307 AlgorithmParameters

def envelope (C d n D : ℕ) : ℕ := 2^(C*(D*logarithm n)^d)
def budget (Q e C d n D : ℕ) : ℕ := Q*(envelope C d n D+1)^e

theorem logarithm_mono {m n : ℕ} (h : m≤n) : logarithm m≤logarithm n := by
  unfold logarithm
  rw [Nat.log2_eq_log_two,Nat.log2_eq_log_two]
  exact Nat.add_le_add_right (Nat.log_mono_right (Nat.mul_le_mul_left 2 h)) 1

theorem envelope_mono (C d D : ℕ) {m n : ℕ} (h : m≤n) : envelope C d m D≤envelope C d n D := by
  apply Nat.pow_le_pow_right (by decide)
  exact Nat.mul_le_mul_left C (Nat.pow_le_pow_left (Nat.mul_le_mul_left D (logarithm_mono h)) d)

/-- One root envelope uniformly bounds every positive-order child node;
the constants are fixed before either root or child is supplied. -/
theorem uniform (a K b : ℕ) (hK : 0<K) :
    ∃ C d : ℕ,0<C ∧ 0<d ∧ ∀ n D m : ℕ,0<D → 0<m → m≤n →
      Lax263307.ParameterResources.resource a K b m D≤envelope C d n D := by
  obtain ⟨C,d,hC,hd,hbound⟩ := Lax263307.ParameterResources.resource_bound a K b hK
  exact ⟨C,d,hC,hd,fun n D m hD hm hmn => (hbound m D hm hD).trans (envelope_mono C d D hmn)⟩

/-- Any fixed polynomial workspace/local-time budget in the root envelope
is absorbed into the same type of quasipolynomial exponent. -/
theorem budget_bound (Q e C d n D : ℕ) (hD : 0<D) :
    budget Q e C d n D≤envelope (Q+e*(C+1)) d n D := by
  let X := D*logarithm n
  have hX : 1≤X := by
    have hp : 0<X := by dsimp [X,logarithm]; positivity
    omega
  have hpow : 1≤X^d := Nat.one_le_pow _ _ hX
  have hp : 2^(C*X^d)+1≤2^(C*X^d+1) := by
    have hh : 1≤2^(C*X^d) := Nat.one_le_pow _ _ (by decide)
    rw [pow_succ]
    omega
  calc
    budget Q e C d n D≤2^Q*(2^(C*X^d+1))^e :=
      Nat.mul_le_mul (Nat.lt_two_pow_self.le) (Nat.pow_le_pow_left hp e)
    _=2^(Q+(C*X^d+1)*e) := by rw [←pow_mul,←pow_add]
    _≤envelope (Q+e*(C+1)) d n D := by
      apply Nat.pow_le_pow_right (by decide)
      change Q+(C*X^d+1)*e≤(Q+e*(C+1))*X^d
      nlinarith only [hpow,Nat.mul_le_mul_left Q hpow,Nat.mul_le_mul_left e hpow]

theorem recursive_bound (Q e C d n D localCost branches : ℕ) (hD : 0<D)
    (hl : localCost≤budget Q e C d n D) (hb : branches≤budget Q e C d n D) :
    NativeRecursionBudget.work localCost branches (RecursionDepth.depth n)≤
      envelope (3*(Q+e*(C+1)+1)) (d+1) n D :=
  NativeRecursionBudget.amplify (Q+e*(C+1)) d n D localCost branches hD
    (hl.trans (budget_bound Q e C d n D hD)) (hb.trans (budget_bound Q e C d n D hD))

end Lax263307Proofs.NativeRootResource
