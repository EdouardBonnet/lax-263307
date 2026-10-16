import Lax263307Proofs.QPTASRuntime
import Mathlib.Tactic

set_option maxRecDepth 10000

namespace Lax263307Proofs.ArchiveRuntime

open QPTASRuntime

/-- For fixed precision, the original stronger bound and the structural
reader/compiler overhead fit the archive's quasipolynomial envelope. -/
theorem bound (c d k a : ℕ) : ∃ q e : ℕ, 0<q ∧ 0<e ∧
    ∀ n ℓ N : ℕ, n≤N → ℓ≤N+k+6 →
      1000*(timeBound c d n ℓ (1/((k:ℚ)+1))+N+k+a+100) ≤
        2^(q*(Nat.log2 (N+2)+1)^e) := by
  let A := c*(k+1)^d+c+(k+9)*d+1
  refine ⟨A+k+a+1104,d+1,by omega,by omega,?_⟩
  intro n ℓ N hn hℓ
  let L := Nat.log2 (N+2)+1
  let F := L^(d+1)
  have hL : 1≤L := by dsimp [L]; omega
  have hF : 1≤F := Nat.one_le_pow _ _ hL
  have hLF : L≤F := le_self_pow hL (by omega)
  have hDF : L^d≤F := Nat.pow_le_pow_right hL (by omega)
  have hlog : Nat.log2 (n+2)+1≤L := by
    have h := Nat.log_mono_right (b:=2) (by omega : n+2≤N+2)
    simpa only [←Nat.log2_eq_log_two] using Nat.add_le_add_right h 1
  have hN : N+1≤2^L := by
    have h : N+2<2^L := Nat.lt_pow_of_log_lt (by decide) (by
      change Nat.log 2 (N+2)<Nat.log2 (N+2)+1
      rw [Nat.log2_eq_log_two]
      omega)
    omega
  have hceil : ⌈(1/((k:ℚ)+1))⁻¹⌉₊=k+1 := by
    rw [one_div, inv_inv, ←Nat.cast_one, ←Nat.cast_add, Nat.ceil_natCast]
  have hfirst : 2^(c*(⌈(1/((k:ℚ)+1))⁻¹⌉₊*(Nat.log2 (n+2)+1))^d) ≤ 2^(A*F) := by
    apply Nat.pow_le_pow_right (by decide)
    rw [hceil, mul_pow, ←mul_assoc]
    have hpow := (Nat.pow_le_pow_left hlog d).trans hDF
    exact (Nat.mul_le_mul_left _ hpow).trans
      (Nat.mul_le_mul_right F (by dsimp [A]; omega))
  have hbase : ℓ+1≤2^(k+8+L) := by
    calc
      ℓ+1 ≤ (k+8)*(N+1) := by nlinarith
      _ ≤ 2^(k+8)*2^L := Nat.mul_le_mul Nat.lt_two_pow_self.le hN
      _ = _ := (pow_add _ _ _).symm
  have hsecond : c*(ℓ+1)^d≤2^(A*F) := by
    calc
      c*(ℓ+1)^d ≤ 2^c*(2^(k+8+L))^d :=
        Nat.mul_le_mul Nat.lt_two_pow_self.le (Nat.pow_le_pow_left hbase d)
      _ = 2^(c+(k+8+L)*d) := by rw [←pow_mul, ←pow_add]
      _ ≤ 2^(A*F) := by
        apply Nat.pow_le_pow_right (by decide)
        have hc := Nat.le_mul_of_pos_right c hF
        have hk := Nat.le_mul_of_pos_right (k+8) hF
        have hx : k+8+L ≤ (k+9)*F := by nlinarith
        have hh := Nat.mul_le_mul_right d hx
        calc
          _ ≤ c*F+(k+9)*F*d := Nat.add_le_add hc hh
          _ = (c+(k+9)*d)*F := by ring
          _ ≤ A*F := Nat.mul_le_mul_right _ (by dsimp [A]; omega)
  have hT : timeBound c d n ℓ (1/((k:ℚ)+1))≤2^(A*F+1) := by
    unfold timeBound
    rw [pow_succ]
    omega
  have hrest : N+k+a+100≤2^((k+a+102)*F) := by
    calc
      N+k+a+100 ≤ (k+a+101)*(N+1) := by nlinarith
      _ ≤ 2^(k+a+101)*2^L := Nat.mul_le_mul Nat.lt_two_pow_self.le hN
      _ = 2^(k+a+101+L) := (pow_add _ _ _).symm
      _ ≤ _ := by
        apply Nat.pow_le_pow_right (by decide)
        have hh := Nat.le_mul_of_pos_right (k+a+101) hF
        nlinarith
  let U := (A+k+a+103)*F
  have hTU : timeBound c d n ℓ (1/((k:ℚ)+1)) ≤ 2^U :=
    hT.trans (Nat.pow_le_pow_right (by decide) (by dsimp [U]; nlinarith))
  have hRU : N+k+a+100≤2^U :=
    hrest.trans (Nat.pow_le_pow_right (by decide) (by dsimp [U]; nlinarith))
  calc
    _ ≤ 1000*(2^U+2^U) := by omega
    _ ≤ 2^1000*2^(U+1) := by
      rw [pow_succ]
      calc
        _ = 1000*(2^U*2) := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (show 1000≤2^1000 from Nat.lt_two_pow_self.le)
    _ = 2^(1000+(U+1)) := (pow_add _ _ _).symm
    _ ≤ _ := by
      apply Nat.pow_le_pow_right (by decide)
      change 1000+(U+1) ≤ (A+k+a+1104)*F
      dsimp [U]
      nlinarith

end Lax263307Proofs.ArchiveRuntime
