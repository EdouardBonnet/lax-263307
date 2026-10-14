import Lax263307Proofs.NativeSmallAttempt
import Lax263307Proofs.NativeRootResource
import Mathlib.Data.Nat.Choose.Bounds

namespace Lax263307Proofs.NativeExhaustiveResources

open Lax263307 AlgorithmParameters ParameterResources

/-- Every binomial table entry fits as soon as vertex masks fit. -/
theorem table_words (B n k : ℕ) (hm : 2^n<B) : ∀ i≤n,∀ j≤k,i.choose j<B := by
  intro i hi j hj
  exact (Nat.choose_le_two_pow i j).trans_lt ((Nat.pow_le_pow_right (by decide) hi).trans_lt hm)

/-- The exhaustive branch enumerates only a root-resource-bounded number
of subsets. The zero/one-vertex shortcut also satisfies this bound. -/
theorem choices_bound (n k threshold R : ℕ) (hn : n≤R)
    (hsmall : k≤threshold ∨ n≤1) (hpower : (n+1)^threshold≤R) : n.choose k≤R+2 := by
  rcases hsmall with hk | hn1
  · have hbase : n^k ≤ (n+1)^k := Nat.pow_le_pow_left (by omega) k
    have hexp : (n+1)^k ≤ (n+1)^threshold := Nat.pow_le_pow_right (by omega) hk
    exact (Nat.choose_le_pow n k).trans (hbase.trans (hexp.trans (by omega)))
  · exact (Nat.choose_le_two_pow n k).trans
      ((Nat.pow_le_pow_right (by decide) hn1).trans (by norm_num))

theorem time_bound (n k threshold R : ℕ) (hn : n≤R) (hk : k≤n)
    (hsmall : k≤threshold ∨ n≤1) (hpower : (n+1)^threshold≤R) :
    NativeExhaustive.cost n k+15*n+20≤300*(R+2)^3 := by
  let S := R+2
  have hS : 1≤S := by dsimp [S]; omega
  have hnS : n≤S := by dsimp [S]; omega
  have hnp : n+1≤S := by dsimp [S]; omega
  have hkp : k+1≤S := by omega
  have hchoices : n.choose k≤S := choices_bound n k threshold R hn hsmall hpower
  have h12 : S≤S^2 := le_self_pow hS (by omega)
  have h23 : S^2≤S^3 := Nat.pow_le_pow_right hS (by omega)
  have h03 : 1≤S^3 := Nat.one_le_pow _ _ hS
  calc
    NativeExhaustive.cost n k+15*n+20 ≤ 54*S^2+(38*S^2+54*S+44)*S+35+15*S+20 := by
      dsimp only [NativeExhaustive.cost]
      have hsq : n*n≤S^2 := by simpa only [pow_two] using Nat.mul_self_le_mul_self hnS
      have htable : (n+1)*(k+1)≤S^2 := by simpa only [pow_two] using Nat.mul_le_mul hnp hkp
      have hb : 38*n*n+54*n+44≤38*S^2+54*S+44 := by nlinarith only [hsq,hnS]
      have hc := Nat.mul_le_mul hb hchoices
      nlinarith only [htable,hc,hnS]
    _ ≤ 300*S^3 := by nlinarith only [h12,h23,h03]
    _ = _ := rfl

/-- The same estimate applies directly to a node under the common root
parameter envelope, including the public algorithm's small-target cutoff. -/
theorem node_time (a K b n D k R : ℕ) (hR : resource a K b n D≤R) (hk : k≤n)
    (hsmall : k≤cutoff a K b n D ∨ n≤1) :
    NativeExhaustive.cost n k+15*n+20≤300*(R+2)^3 := by
  apply time_bound n k (cutoff a K b n D) R _ hk hsmall
  · dsimp only [resource] at hR; omega
  · dsimp only [resource] at hR; omega

end Lax263307Proofs.NativeExhaustiveResources
