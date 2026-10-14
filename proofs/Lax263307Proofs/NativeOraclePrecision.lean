import Lax263307Proofs.NativeProjectionQueryBounds
import Lax263307Proofs.NativeNormalHeight
import Lax263307Proofs.NativeEncodedLP
import Lax263307Proofs.NativeFlowQueryResources

namespace Lax263307Proofs.NativeOraclePrecision

open Lax263307 Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax109476.RationalEncoding Lax759944.BinaryWordEncoding
open Lax759944.RamPolytime

/-- The chosen solver's actual output word width; independent of host width. -/
def OutputWidth (f : List ℕ → List ℕ) (wp : Polynomial ℕ) : Prop :=
  ∀ xs,FitsInWords (wp.eval (bitSize xs)) (f xs)

theorem exists_output_width (f : List ℕ → List ℕ) (hf : RamPolytime f) :
    ∃ wp : Polynomial ℕ,OutputWidth f wp := by
  obtain ⟨p,wp,tp,hcall⟩ := hf
  exact ⟨wp,fun xs v hv => (hcall xs).1 v (List.mem_append_right _ hv)⟩

def certificateHeight (wp : Polynomial ℕ) (R : ℕ) : ℕ :=
  wp.eval (NativeProjectionQueryBounds.queryBound R)

def roundedHeight (wp : Polynomial ℕ) (R : ℕ) : ℕ :=
  80*(R+1)+(R+1)*(2*certificateHeight wp R+1)+2*R+1

theorem height_mono (q : ℚ) (h H : ℕ) (hq : NativeRoundedStep.height q h) (hh : h≤H) :
    NativeRoundedStep.height q H := by
  have hp : 2^h≤2^H := Nat.pow_le_pow_right (by decide) hh
  exact ⟨hq.1.trans hp,hq.2.trans hp⟩

/-- The canonical certificate coordinates fit a root polynomial height,
using the actual solver output and the checked query-size estimate. -/
theorem certificate_bound (f : List ℕ → List ℕ) (wp : Polynomial ℕ)
    (he : NativeEncodedLP.Encoded f) (hw : OutputWidth f wp)
    {m n : ℕ} (P : Program ℚ m n) (x : Fin n → ℚ) (R : ℕ)
    (hquery : bitSize (encodeProgram (DistanceProjection.distanceProgram P x))≤
      NativeProjectionQueryBounds.queryBound R) :
    NativeProjectionResult.CertificateBounded (2^certificateHeight wp R)
      (RegisteredLP.certificate f (DistanceProjection.distanceProgram P x)) := by
  apply NativeProjectionOracle.certificate_bound
  intro v hv
  have hv' : v∈f (encodeProgram (DistanceProjection.distanceProgram P x)) := by
    rwa [(he _ _ (DistanceProjection.distanceProgram P x)).1]
  have hfit := hw _ v hv'
  have hpoly := NativeFlowQueryResources.eval_mono wp hquery
  exact hfit.le.trans (Nat.pow_le_pow_right (by decide) hpoly)

/-- Both source-normal subtraction and denominator clearing are paid in
the fixed root height, not in the possibly much larger host word width. -/
theorem far_height (f : List ℕ → List ℕ) (wp : Polynomial ℕ)
    (he : NativeEncodedLP.Encoded f) (hw : OutputWidth f wp)
    {m n : ℕ} (P : Program ℚ m n) (x : Fin n → ℚ) (ρ : ℚ) (R : ℕ) (hn : n≤R)
    (hquery : bitSize (encodeProgram (DistanceProjection.distanceProgram P x))≤
      NativeProjectionQueryBounds.queryBound R)
    (a : Fin n → ℚ) (β : ℚ)
    (hfar : RationalProjection.classify P ρ
      (RegisteredLP.certificate f (DistanceProjection.distanceProgram P x))=.far a β) :
    ∀ i,NativeRoundedStep.height (RoundedOracleSearch.rationalNormal (RationalCutBuffer.integerNormal a) i)
      (roundedHeight wp R) := by
  let H := certificateHeight wp R
  have hc := certificate_bound f wp he hw P x R hquery
  have ha := NativeNormalHeight.far_height (2^H) P ρ _ hc a β hfar
  have hpow : 2*(2^H)^2=2^(2*H+1) := by
    calc
      _=(2^H)^2*2 := Nat.mul_comm _ _
      _=2^(H*2)*2 := by rw [pow_mul]
      _=2^(H*2+1) := (pow_succ _ _).symm
      _=_ := by congr 1; omega
  rw [hpow] at ha
  have cleared := NativeNormalHeight.cleared_height n (2*H+1) a ha
  intro i
  apply height_mono _ _ _ (cleared i)
  have hp := Nat.mul_le_mul_right (2*H+1) (Nat.add_le_add_right hn 1)
  dsimp [roundedHeight]
  change (n+1)*(2*H+1)≤80*(R+1)+(R+1)*(2*H+1)+2*R+1
  omega

theorem component_height (wp : Polynomial ℕ) {n r : ℕ} (A C : Finset (Fin n)) (u R : ℕ)
    (hu : u≤n) (hn : n≤R) :
    ∀ i,NativeRoundedStep.height (RoundedOracleSearch.rationalNormal (RationalCutBuffer.integerNormal
      (RoundedOracleSearch.rationalNormal (NativeComponentNormal.normal (r:=r) A C u))) i) (roundedHeight wp R) := by
  intro i
  exact height_mono _ _ _ (NativeNormalHeight.component_height A C u hu i) (by dsimp [roundedHeight]; omega)

end Lax263307Proofs.NativeOraclePrecision
