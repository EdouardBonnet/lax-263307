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


def certificateHeight (wp : Polynomial ℕ) (R : ℕ) : ℕ :=
  wp.eval (NativeProjectionQueryBounds.queryBound R)

def roundedHeight (wp : Polynomial ℕ) (R : ℕ) : ℕ :=
  80*(R+1)+(R+1)*(2*certificateHeight wp R+1)+2*R+1

theorem height_mono (q : ℚ) (h H : ℕ) (hq : NativeRoundedStep.height q h) (hh : h≤H) :
    NativeRoundedStep.height q H := by
  have hp : 2^h≤2^H := Nat.pow_le_pow_right (by decide) hh
  exact ⟨hq.1.trans hp,hq.2.trans hp⟩


theorem component_height (wp : Polynomial ℕ) {n r : ℕ} (A C : Finset (Fin n)) (u R : ℕ)
    (hu : u≤n) (hn : n≤R) :
    ∀ i,NativeRoundedStep.height (RoundedOracleSearch.rationalNormal (RationalCutBuffer.integerNormal
      (RoundedOracleSearch.rationalNormal (NativeComponentNormal.normal (r:=r) A C u))) i) (roundedHeight wp R) := by
  intro i
  exact height_mono _ _ _ (NativeNormalHeight.component_height A C u hu i) (by dsimp [roundedHeight]; omega)

end Lax263307Proofs.NativeOraclePrecision
