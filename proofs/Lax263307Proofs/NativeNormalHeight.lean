import Lax263307Proofs.NativeCutResources
import Lax263307Proofs.NativeProjectionOracle
import Lax263307Proofs.NativeRationalBounds
import Lax263307Proofs.NativeComponentNormal
import Lax263307.NativeRoundedStep

namespace Lax263307Proofs.NativeNormalHeight

open Lax263307 RoundedOracleSearch RationalProjection DistanceProjection
open Lax109476.LinearProgram Lax109476.RationalCertificates
open NativeSignedArithmetic

/-- The actual far normal is a difference of two certificate coordinates. -/
theorem far_height {m n : ℕ} (M : ℕ) (P : Program ℚ m n) (ρ : ℚ)
    (c : Certificate (m+(n+n)) (n+1)) (hc : NativeProjectionResult.CertificateBounded M c)
    (a : Fin n → ℚ) (β : ℚ) (he : classify P ρ c=.far a β) :
    ∀ i,Bounded (2*M^2) (a i) := by
  cases c with
  | infeasible y => simp [classify] at he
  | unbounded z y => simp [classify] at he
  | optimal z y =>
    dsimp only [classify] at he
    split at he
    · contradiction
    · cases he
      intro i
      exact NativeRationalBounds.subtract M _ _ (hc.2 _) (hc.2 _)

/-- Clearing denominators increases normal-height bits only linearly in
the dimension. This applies to the actual certificate-derived far cut. -/
theorem cleared_height (n h : ℕ) (a : Fin n → ℚ) (ha : ∀ i,Bounded (2^h) (a i)) :
    ∀ i,NativeRoundedStep.height (rationalNormal (RationalCutBuffer.integerNormal a) i) ((n+1)*h) := by
  intro i
  have hn := NativeCutResources.integer_height n h a ha i
  simp only [NativeRoundedStep.height,rationalNormal,Rat.num_intCast,Rat.den_intCast]
  exact ⟨hn,Nat.one_le_two_pow⟩

theorem coefficient_bound {n r : ℕ} (A C : Finset (Fin n)) (u : ℕ)
    (T : LinearRelaxation.Coordinate n r) : (ComponentCutEncoding.coefficient A C u T).natAbs≤C.card+u := by
  have hsum : (∑ v∈C,(if insert v A=T.val then (1 : ℤ) else 0)).natAbs≤C.card := by
    calc
      _ ≤ ∑ v∈C,(if insert v A=T.val then (1 : ℤ) else 0).natAbs := Int.natAbs_sum_le C _
      _ ≤ ∑ _v∈C,(1 : ℕ) := Finset.sum_le_sum (by intro v _; split_ifs <;> norm_num)
      _ = _ := by simp
  have hu : (if A=T.val then (u : ℤ) else 0).natAbs≤u := by split_ifs <;> simp
  exact (Int.natAbs_sub_le _ _).trans (Nat.add_le_add hsum hu)

/-- The failed-child normal is already integral, so clearing it does not
increase its height. Its true height is controlled by vertex order. -/
theorem component_height {n r : ℕ} (A C : Finset (Fin n)) (u : ℕ) (hu : u≤n) :
    ∀ i,NativeRoundedStep.height
      (rationalNormal (RationalCutBuffer.integerNormal (rationalNormal (NativeComponentNormal.normal (r:=r) A C u))) i)
      (2*n+1) := by
  rw [NativeComponentNormal.cleared_integer]
  intro i
  have hcoef := coefficient_bound A C u (CoordinateCatalog.indexing n r i)
  have hcard := NativeMaskUnpack.card_bound C
  have hn : (NativeComponentNormal.normal (r:=r) A C u i).natAbs≤2*n := by
    change (ComponentCutEncoding.coefficient A C u (CoordinateCatalog.indexing n r i)).natAbs≤2*n
    omega
  simp only [NativeRoundedStep.height,rationalNormal,Rat.num_intCast,Rat.den_intCast]
  exact ⟨hn.trans (Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by decide) (by omega))),Nat.one_le_two_pow⟩

end Lax263307Proofs.NativeNormalHeight
