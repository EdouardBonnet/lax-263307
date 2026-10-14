import Lax263307Proofs.RoundedOracleSearch
import Lax263307Proofs.NativeSignedArithmetic
import Lax263307.NativeRoundedStep
import Lax455465Proofs.WordSize

namespace Lax263307Proofs.NativeTrajectoryResources

open Lax263307 RoundedOracleSearch Matrix
open Lax109476.RationalEncoding Lax109476.RationalCertificates Lax109476Proofs.EllipsoidRounding
open Lax759944.BinaryWordEncoding

/-- Convert the registered bit-size estimate into the numeric rational
height used by the native arithmetic and rounded-update interfaces. -/
theorem height_of_encoding (q : ℚ) (h : ℕ) (hh : bitSize (encodeRational q)≤h) :
    NativeRoundedStep.height q h := by
  have hn := Lax455465Proofs.WordSize.member_bound (encodeRational q) q.num.natAbs
    (by simp [encodeRational])
  have hd := Lax455465Proofs.WordSize.member_bound (encodeRational q) q.den
    (by simp [encodeRational])
  exact ⟨hn.le.trans (Nat.pow_le_pow_right (by decide) hh),
    hd.le.trans (Nat.pow_le_pow_right (by decide) hh)⟩

/-- One root polynomial height covers every stored state at every local
iteration, uniformly in the actual (possibly much larger) cut normals. -/
theorem state_height {n : ℕ} {Result : Type} (hn : 2≤n)
    (oracle : ℕ → (Fin n → ℚ) → Reply n Result)
    (nonzero : ∀ k center a,oracle k center=.cut a → ∃ i,a i≠0)
    (R k : ℕ) (hnR : n≤R) (hkR : k≤R) :
    (∀ i j,NativeRoundedStep.height ((trajectory oracle k).1 i j) (80*(R+1))) ∧
    (∀ i,NativeRoundedStep.height ((trajectory oracle k).2 i) (80*(R+1))) := by
  constructor
  · intro i j
    apply height_of_encoding
    exact (Lax263307.RoundedOracleSearch.shape_encoding_bound hn oracle nonzero k i j).trans (by omega)
  · intro i
    apply height_of_encoding
    exact (Lax263307.RoundedOracleSearch.center_encoding_bound hn oracle nonzero k i).trans (by omega)

/-- The current shape is positive definite at every reached iteration. -/
theorem shape_posDef {n : ℕ} {Result : Type} (hn : 2≤n)
    (oracle : ℕ → (Fin n → ℚ) → Reply n Result)
    (nonzero : ∀ k center a,oracle k center=.cut a → ∃ i,a i≠0) (k : ℕ) :
    (realShape (trajectory oracle k).1).PosDef := by
  rw [(Lax263307Proofs.RoundedOracleSearch.trajectory_eq_sequences oracle k).1]
  exact (Lax109476Proofs.EllipsoidSequence.shapes_invariant n hn
    (fun j => rationalNormal (normalSchedule oracle j))
    (fun j => Lax263307Proofs.RoundedOracleSearch.schedule_norm (by omega) oracle nonzero j) k).1

/-- The actual cut satisfies the strictly positive quadratic-form guard
required by the rounded native update; no positivity advice is supplied. -/
theorem update_positive {n : ℕ} {Result : Type} (hn : 2≤n)
    (oracle : ℕ → (Fin n → ℚ) → Reply n Result)
    (nonzero : ∀ k center a,oracle k center=.cut a → ∃ i,a i≠0)
    (k : ℕ) (a : Fin n → ℤ) (ha : oracle k (trajectory oracle k).2=.cut a) :
    0<rationalNormal a ⬝ᵥ ((trajectory oracle k).1 *ᵥ rationalNormal a) := by
  have hne : realVector (rationalNormal a)≠0 := by
    obtain ⟨i,hi⟩ := nonzero k _ a ha
    intro he
    have hi0 := congrFun he i
    have : a i=0 := by simpa [realVector,rationalNormal] using hi0
    exact hi this
  have hpos : (0 : ℝ)<realVector (rationalNormal a) ⬝ᵥ
      (realShape (trajectory oracle k).1 *ᵥ realVector (rationalNormal a)) := by
    simpa using (shape_posDef hn oracle nonzero k).dotProduct_mulVec_pos hne
  have hcast : ((rationalNormal a ⬝ᵥ ((trajectory oracle k).1 *ᵥ rationalNormal a) : ℚ) : ℝ)=
      realVector (rationalNormal a) ⬝ᵥ (realShape (trajectory oracle k).1 *ᵥ realVector (rationalNormal a)) := by
    simp [dotProduct,mulVec,realVector,realShape]
  rw [←hcast] at hpos
  exact_mod_cast hpos

end Lax263307Proofs.NativeTrajectoryResources
