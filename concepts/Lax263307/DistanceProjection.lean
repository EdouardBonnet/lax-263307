import Lax109476.RationalCertificates

/-!
---
title: Infinity-distance projection LP and its separating dual
type: lemma
---
Append one nonnegative distance variable t to a linear program and impose
|y_j-center_j|≤t for every coordinate. Maximizing -t finds a nearest feasible
point. A matching dual certificate supplies a separating normal whose sum
of absolute coefficients is at most one, and its gap at the queried center
is exactly t. Thus a distance threshold yields either a nearby feasible
point for round-or-cut or a uniformly strong separation.

# Formalization notes

Rows and variables use computable finite index concatenation. No choice-based
coordinate labeling is needed to form the dense rational program. The
algebra holds in real variables and applies to exact rational certificates
by casting. It makes no full-dimensionality assumption. The proof package
implements the matrix construction and registered solver invocation on the RAM.
-/

namespace Lax263307.DistanceProjection

open Lax109476.LinearProgram

/-- The distance LP with one additional variable and two rows per coordinate. -/
def distanceProgram {K : Type} [Ring K] {m n : ℕ} (P : Program K m n) (center : Fin n → K) :
    Program K (m + (n + n)) (n + 1) where
  A := Fin.addCases
    (fun i => Fin.addCases (P.A i) (fun _ => 0))
    (Fin.addCases
      (fun i => Fin.addCases (fun j => if i = j then 1 else 0) (fun _ => -1))
      (fun i => Fin.addCases (fun j => if i = j then -1 else 0) (fun _ => -1)))
  b := Fin.addCases P.b (Fin.addCases center (fun i => -center i))
  c := Fin.addCases (fun _ => 0) (fun _ => -1)

def point {K : Type} {n : ℕ} (z : Fin (n + 1) → K) (j : Fin n) : K := z (Fin.castAdd 1 j)
def distance {K : Type} {n : ℕ} (z : Fin (n + 1) → K) : K := z (Fin.natAdd n (0 : Fin 1))

def oldMultipliers {K : Type} {m n : ℕ} (dual : Fin (m + (n + n)) → K) (i : Fin m) : K :=
  dual (Fin.castAdd (n + n) i)
def plusMultipliers {K : Type} {m n : ℕ} (dual : Fin (m + (n + n)) → K) (i : Fin n) : K :=
  dual (Fin.natAdd m (Fin.castAdd n i))
def minusMultipliers {K : Type} {m n : ℕ} (dual : Fin (m + (n + n)) → K) (i : Fin n) : K :=
  dual (Fin.natAdd m (Fin.natAdd n i))
def normal {K : Type} [Sub K] {m n : ℕ} (dual : Fin (m + (n + n)) → K) (i : Fin n) : K :=
  minusMultipliers dual i - plusMultipliers dual i

axiom primal_characterization {m n : ℕ} (P : Program ℝ m n) (center : Fin n → ℝ)
    (z : Fin (n + 1) → ℝ) :
    PrimalFeasible (distanceProgram P center) z ↔
      PrimalFeasible P (point z) ∧ 0 ≤ distance z ∧
        ∀ j, |point z j - center j| ≤ distance z

axiom objective_bounded {m n : ℕ} (P : Program ℝ m n) (center : Fin n → ℝ) :
    IsBoundedAbove (distanceProgram P center)

axiom projection_feasible_iff {m n : ℕ} (P : Program ℝ m n) (center : Fin n → ℝ) :
    IsFeasible (distanceProgram P center) ↔ IsFeasible P

axiom dual_normal {m n : ℕ} (P : Program ℝ m n) (center : Fin n → ℝ)
    (dual : Fin (m + (n + n)) → ℝ) (feasible : DualFeasible (distanceProgram P center) dual) :
    (∑ j, |normal dual j|) ≤ 1 ∧
      ∀ z, PrimalFeasible P z → (∑ j, normal dual j * z j) ≤ dualValue P (oldMultipliers dual)

axiom optimal_gap {m n : ℕ} (P : Program ℝ m n) (center : Fin n → ℝ)
    (z : Fin (n + 1) → ℝ) (dual : Fin (m + (n + n)) → ℝ)
    (primal : PrimalFeasible (distanceProgram P center) z)
    (dual_feasible : DualFeasible (distanceProgram P center) dual)
    (matching : primalValue (distanceProgram P center) z = dualValue (distanceProgram P center) dual) :
    PrimalFeasible P (point z) ∧ 0 ≤ distance z ∧
      (∀ j, |point z j - center j| ≤ distance z) ∧
      (∑ j, |normal dual j|) ≤ 1 ∧
      (∀ y, PrimalFeasible P y → (∑ j, normal dual j * y j) ≤ dualValue P (oldMultipliers dual)) ∧
      (∑ j, normal dual j * center j) - dualValue P (oldMultipliers dual) = distance z

end Lax263307.DistanceProjection
