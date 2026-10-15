import Lax263307.NearOracle
import Lax263307.RegisteredLP
import Lax263307.RationalProjection
import Lax263307.RationalCutBuffer

/-!
---
title: The projected round-or-cut search
type: definition
---
The oracle decodes an LP certificate and either rejects the relaxation,
returns a separating projection cut, or invokes the near-relaxation oracle.
A bounded rounded-ellipsoid search repeats this step.

The correctness predicates describe the approximation guarantee and the
protected region that every returned cut must preserve. A failed search
certifies that the independence number is below the requested target.

# Formalization notes

The definitions take the LP solver, flow solver, and recursive child queries
as arguments. Precision and iteration limits are explicit functions of the
class constants, graph order, and accuracy denominator.
-/

namespace Lax263307.ProjectedOracle

open BufferedEllipsoid (scale)
open ComponentCutEncoding (coefficient)
open DistanceProjection (distanceProgram)
open MomentLP (Index decode dimension encode program)
open RationalCutBuffer (integerNormal)
open RationalProjection (classify)
open RegisteredLP (certificate)
open RoundedOracleSearch (Reply rationalNormal)
open LinearRelaxation AlgorithmParameters

def tolerance (a K B n D : ℕ) : ℚ := momentFloor a K B n D / (32 * (n : ℚ)^2 * (D : ℚ)^2)

def raw {N : ℕ} (center : Fin N → ℚ) : Fin N → ℚ := fun i => 4 * (N : ℚ) * center i

def run {n : ℕ} (lp flow : List ℕ → List ℕ) (a K B D : ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ)
    (child : Finset (Fin n) → ℕ → Option (Finset (Fin n)))
    (center : Index n (level a K B n D) → ℚ) :
    Reply (dimension n (level a K B n D)) (Finset (Fin n)) :=
  let P := program G k (level a K B n D)
  match classify P (tolerance a K B n D)
    (certificate lp (distanceProgram P (raw center))) with
  | .reject => .reject
  | .far normal _ => .cut (integerNormal normal)
  | .near y =>
    match NearOracle.run flow a K B D G k (decode y) child with
    | .reject => .reject
    | .found I => .found I
    | .cut A C u => .cut (integerNormal
        (rationalNormal (encode (coefficient A C u))))

def Good {n : ℕ} (G : SimpleGraph (Fin n)) (k h D : ℕ) (I : Finset (Fin n)) : Prop :=
  G.IsIndepSet (I : Set (Fin n)) ∧ (1 - 4 * (1 / (D : ℝ))) ^ (h+1) * (k : ℝ) ≤ I.card

def Correct {n : ℕ} (G : SimpleGraph (Fin n)) (k h a K B D : ℕ)
    (center : Index n (level a K B n D) → ℚ) :
    Reply (dimension n (level a K B n D)) (Finset (Fin n)) → Prop
  | .found I => Good G k h D I
  | .reject => independentSetHull G k (level a K B n D) = ∅
  | .cut normal => (∃ i, normal i ≠ 0) ∧
    ∀ z ∈ independentSetHull G k (level a K B n D),
    ∀ e : Index n (level a K B n D) → ℝ,
    (∀ i, |e i| ≤ ((2 : ℝ) ^ precision a K B n D)⁻¹) →
      (fun i => (normal i : ℝ)) ⬝ᵥ
        (scale (encode z) + e - (fun i => (center i : ℝ))) ≤ 0

def search {n : ℕ} (lp flow : List ℕ → List ℕ) (a K B D : ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ)
    (child : Finset (Fin n) → ℕ → Option (Finset (Fin n))) : Option (Finset (Fin n)) :=
  RoundedOracleSearch.search (fun _ center => run lp flow a K B D G k child center)
    (precision a K B n D)

def SearchCorrect {n : ℕ} (G : SimpleGraph (Fin n)) (k h D : ℕ) : Option (Finset (Fin n)) → Prop
  | some I => Good G k h D I
  | none => IsIndependenceBound G Finset.univ (k-1)

end Lax263307.ProjectedOracle
