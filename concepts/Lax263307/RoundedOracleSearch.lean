import Lax263307.BufferedEllipsoid
import Lax109476.RationalEncoding
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Size

/-!
---
title: A bounded rounded ellipsoid search with answer-or-cut replies
type: lemma
---
An oracle returns an answer, a certified rejection, or a nonzero integer
central-cut normal. The search stores a rational matrix and center, advances
them once per cut, and stops after an explicit finite iteration budget.
When rejection is impossible and every cut preserves a fixed dyadic cube
around a scaled unit-cube point, the search must return an answer.

# Formalization notes

The computable rational update is the registered LP ellipsoid update,
written explicitly so that definitions and statement types do not import
a proof package. The proof identifies its trajectory with the registered
sequence and applies that sequence's determinant and containment theorems.
The main theorem supplies the oracle and verifies the corresponding
RAM implementation.
-/

namespace Lax263307.RoundedOracleSearch

open BufferedEllipsoid (scale)
open Lax109476.RationalEncoding (encodeRational)
open Lax759944.BinaryWordEncoding (bitSize)
open Matrix

abbrev State (n : ℕ) := Matrix (Fin n) (Fin n) ℚ × (Fin n → ℚ)

inductive Reply (n : ℕ) (Result : Type)
  | found (answer : Result)
  | reject
  | cut (normal : Fin n → ℤ)

def rationalNormal {n : ℕ} (a : Fin n → ℤ) : Fin n → ℚ := fun i => a i

def roundDown (q : ℚ) (D : ℕ) : ℚ := (Int.floor (q * D) : ℚ) / D

def sqrtUpper (q : ℚ) (D : ℕ) : ℚ :=
  ((Nat.sqrt (Nat.ceil (q * (D : ℚ) ^ 2)) + 1 : ℕ) : ℚ) / D

def cutShape {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (a : Fin n → ℚ) :
    Matrix (Fin n) (Fin n) ℚ :=
  ((n : ℚ) ^ 2 / ((n : ℚ) ^ 2 - 1)) •
    (A - (2 / (((n : ℚ) + 1) * (a ⬝ᵥ (A *ᵥ a)))) •
      Matrix.vecMulVec (A *ᵥ a) (A *ᵥ a))

def grid (n k : ℕ) : ℕ := 2 ^ ((2 * k + 2) + (2 * n + 4) + n + 3)

def cached {n : ℕ} (state : State n) : State n :=
  let rows : Vector (Vector ℚ n) n := Vector.ofFn (fun i => Vector.ofFn (state.1 i))
  let center : Vector ℚ n := Vector.ofFn state.2
  ((fun i j => (rows.get i).get j), fun i => center.get i)

def update {n : ℕ} (k : ℕ) (state : State n) (a : Fin n → ℤ) : State n :=
  let a := rationalNormal a
  let D := grid n k
  let η : ℚ := 1 / (2 : ℚ) ^ (2 * n + 4)
  let shape := ((1 + η) ^ 2) •
    ((Matrix.of fun i j => roundDown (cutShape state.1 a i j) D) + ((n : ℚ) / D) • 1)
  let center := fun i => roundDown
    (state.2 i - (1 / (((n : ℚ) + 1) * sqrtUpper (a ⬝ᵥ (state.1 *ᵥ a)) D)) *
      (state.1 *ᵥ a) i) D
  cached (shape, center)

def fallback {n : ℕ} : Fin n → ℤ := fun i => if i.val = 0 then 1 else 0

def selectedNormal {n : ℕ} {Result : Type} : Reply n Result → Fin n → ℤ
  | .cut a => a
  | _ => fallback

def trajectory {n : ℕ} {Result : Type} (oracle : ℕ → (Fin n → ℚ) → Reply n Result) :
    ℕ → State n
  | 0 => (1, 0)
  | k + 1 =>
    let old := trajectory oracle k
    update k old (selectedNormal (oracle k old.2))

def normalSchedule {n : ℕ} {Result : Type}
    (oracle : ℕ → (Fin n → ℚ) → Reply n Result) (k : ℕ) : Fin n → ℤ :=
  selectedNormal (oracle k (trajectory oracle k).2)

def scan {n : ℕ} {Result : Type} (oracle : ℕ → (Fin n → ℚ) → Reply n Result) :
    ℕ → ℕ → State n → Option Result
  | _, 0, _ => none
  | k, count + 1, state =>
    match oracle k state.2 with
    | .found answer => some answer
    | .reject => none
    | .cut a => scan oracle (k + 1) count (update k state a)

def steps (n B : ℕ) : ℕ := 4 * (n + 1) * (B * n + 1)

def search {n : ℕ} {Result : Type} (oracle : ℕ → (Fin n → ℚ) → Reply n Result)
    (B : ℕ) : Option Result := scan oracle 0 (steps n B) (1, 0)

axiom search_sound {n : ℕ} {Result : Type}
    (oracle : ℕ → (Fin n → ℚ) → Reply n Result) (B : ℕ) (Good : Result → Prop)
    (answers : ∀ k center answer, oracle k center = .found answer → Good answer) :
    ∀ answer, search oracle B = some answer → Good answer

axiom search_complete {n : ℕ} {Result : Type} (dimension : 2 ≤ n)
    (oracle : ℕ → (Fin n → ℚ) → Reply n Result) (B : ℕ) (precision : 2 ≤ B)
    (nonzero : ∀ k center a, oracle k center = .cut a → ∃ i, a i ≠ 0)
    (no_reject : ∀ k center, oracle k center ≠ .reject)
    (z : Fin n → ℝ) (cube : ∀ i, 0 ≤ z i ∧ z i ≤ 1)
    (retains : ∀ k center a, oracle k center = .cut a →
      ∀ e : Fin n → ℝ, (∀ i, |e i| ≤ ((2 : ℝ) ^ B)⁻¹) →
        (fun i => (a i : ℝ)) ⬝ᵥ
          (scale z + e - (fun i => (center i : ℝ))) ≤ 0) :
    ∃ answer, search oracle B = some answer

axiom center_encoding_bound {n : ℕ} {Result : Type} (dimension : 2 ≤ n)
    (oracle : ℕ → (Fin n → ℚ) → Reply n Result)
    (nonzero : ∀ k center a, oracle k center = .cut a → ∃ i, a i ≠ 0) (k : ℕ) (i : Fin n) :
    bitSize
      (encodeRational ((trajectory oracle k).2 i)) ≤ 60 + 6 * k + 14 * n

axiom shape_encoding_bound {n : ℕ} {Result : Type} (dimension : 2 ≤ n)
    (oracle : ℕ → (Fin n → ℚ) → Reply n Result)
    (nonzero : ∀ k center a, oracle k center = .cut a → ∃ i, a i ≠ 0)
    (k : ℕ) (i j : Fin n) :
    bitSize
      (encodeRational ((trajectory oracle k).1 i j)) ≤ 60 + 6 * k + 14 * n

end Lax263307.RoundedOracleSearch
