import Lax263307.NearOracle
import Lax263307.RegisteredLP
import Lax263307.RationalProjection
import Lax263307.RationalCutBuffer

/-!
---
title: The bounded projected round-or-cut search
type: theorem
---
The actual registered LP certificate decides whether to reject, separate
by a projection cut, or call the computed near-relaxation oracle.
Both cut branches preserve the same explicit dyadic cube about every
scaled independent-set encoding. The bounded rounded ellipsoid loop
therefore returns an approximate independent set or a valid upper bound
strictly below the requested positive target.

# Formalization notes

The only recursive hypothesis concerns answers on balanced child parts.
The LP and flow functions are fixed for the class and have the registered
RAM polynomial-time guarantees. The surrounding computable search still
needs its own finite RAM implementation and time bound.
-/

namespace Lax263307.ProjectedOracle

open LinearRelaxation AlgorithmParameters

def tolerance (a K B n D : ℕ) : ℚ := momentFloor a K B n D / (32 * (n : ℚ)^2 * (D : ℚ)^2)

def raw {N : ℕ} (center : Fin N → ℚ) : Fin N → ℚ := fun i => 4 * (N : ℚ) * center i

def run {n : ℕ} (lp flow : List ℕ → List ℕ) (a K B D : ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ)
    (child : Finset (Fin n) → ℕ → Option (Finset (Fin n)))
    (center : MomentLP.Index n (level a K B n D) → ℚ) :
    RoundedOracleSearch.Reply (MomentLP.dimension n (level a K B n D)) (Finset (Fin n)) :=
  let P := MomentLP.program G k (level a K B n D)
  match RationalProjection.classify P (tolerance a K B n D)
    (RegisteredLP.certificate lp (DistanceProjection.distanceProgram P (raw center))) with
  | .reject => .reject
  | .far normal _ => .cut (RationalCutBuffer.integerNormal normal)
  | .near y =>
    match NearOracle.run flow a K B D G k (MomentLP.decode y) child with
    | .reject => .reject
    | .found I => .found I
    | .cut A C u => .cut (RationalCutBuffer.integerNormal
        (RoundedOracleSearch.rationalNormal (MomentLP.encode (ComponentCutEncoding.coefficient A C u))))

def Good {n : ℕ} (G : SimpleGraph (Fin n)) (k h D : ℕ) (I : Finset (Fin n)) : Prop :=
  G.IsIndepSet (I : Set (Fin n)) ∧ (1 - 4 * (1 / (D : ℝ))) ^ (h+1) * (k : ℝ) ≤ I.card

def Correct {n : ℕ} (G : SimpleGraph (Fin n)) (k h a K B D : ℕ)
    (center : MomentLP.Index n (level a K B n D) → ℚ) :
    RoundedOracleSearch.Reply (MomentLP.dimension n (level a K B n D)) (Finset (Fin n)) → Prop
  | .found I => Good G k h D I
  | .reject => independentSetHull G k (level a K B n D) = ∅
  | .cut normal => (∃ i, normal i ≠ 0) ∧
    ∀ z ∈ independentSetHull G k (level a K B n D),
    ∀ e : MomentLP.Index n (level a K B n D) → ℝ,
    (∀ i, |e i| ≤ ((2 : ℝ) ^ precision a K B n D)⁻¹) →
      (fun i => (normal i : ℝ)) ⬝ᵥ
        (BufferedEllipsoid.scale (MomentLP.encode z) + e - (fun i => (center i : ℝ))) ≤ 0

def search {n : ℕ} (lp flow : List ℕ → List ℕ) (a K B D : ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ)
    (child : Finset (Fin n) → ℕ → Option (Finset (Fin n))) : Option (Finset (Fin n)) :=
  RoundedOracleSearch.search (fun _ center => run lp flow a K B D G k child center)
    (precision a K B n D)

def SearchCorrect {n : ℕ} (G : SimpleGraph (Fin n)) (k h D : ℕ) : Option (Finset (Fin n)) → Prop
  | some I => Good G k h D I
  | none => IsIndependenceBound G Finset.univ (k-1)

open GraphClasses PowerBagBounds

axiom exists_search (C : GraphClass) (hereditary : IsHereditary C)
    (a A : ℕ) (ha : 0 < a) (hA : 0 < A) (class_bound : HasPowerBagBound C a A) :
    ∃ (lp flow : List ℕ → List ℕ) (K B : ℕ),
      Lax759944.RamPolytime.RamPolytime lp ∧ Lax759944.RamPolytime.RamPolytime flow ∧
      0 < K ∧ 0 < B ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G ∈ C n → 0 < n → ∀ (D k h : ℕ), 4 ≤ D → cutoff a K B n D < k →
      ∀ (child : Finset (Fin n) → ℕ → Option (Finset (Fin n))),
      Lax263307.NearOracle.ChildCorrect G D h child →
      SearchCorrect G k h D (search lp flow a K B D G k child)

end Lax263307.ProjectedOracle
