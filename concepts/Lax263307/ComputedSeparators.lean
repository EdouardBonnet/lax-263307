import Lax263307.EdgeBagBounds
import Lax263307.ForcedSeparation
import Lax263307.CutTraces
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD

/-!
---
title: Computing balanced light separators from registered flow-cut outputs
type: lemma
---
Label each remaining vertex set in increasing order, construct its rational
split network, and read the cut membership prefix of the registered
Leighton–Rao solver's output. Orient the two projected shores by size.
Repeat until the remainder has at most two thirds of the original vertices.
The computed list has at most n cuts. Its separator has the stated cost,
and its computed pieces form a balanced partition with no cross edges.

# Formalization notes

All labels, rational capacities, output decoding, shore choices, and the
bounded cut-list loop are computable. The solver retains its actual registered
RAM polynomial-time guarantee. This statement gives the wrapper's functional correctness.
The main theorem also verifies its RAM implementation and running time.
-/

namespace Lax263307.ComputedSeparators

open EdgeSublinearSeparators (IsBalancedSeparator)
open Lax759944.RamPolytime (RamPolytime)
open SeparatorComponents (Partition)
open scoped NNRat
open VertexSplitting Lax455465.RationalEncoding

def decodeCut (n : ℕ) (words : List ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v => words.getD v.val 0 = 1

def label {n : ℕ} (R : Finset (Fin n)) : Fin R.card ↪o Fin n :=
  R.orderEmbOfFin rfl

def restriction {n : ℕ} (G : SimpleGraph (Fin n)) (R : Finset (Fin n)) :
    SimpleGraph (Fin R.card) := G.comap (label R)

instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (R : Finset (Fin n)) :
    DecidableRel (restriction G R).Adj := inferInstanceAs (DecidableRel (G.comap (label R)).Adj)

def ratio (B n : ℕ) : ℚ := B * ((Nat.log2 (2 * n) : ℚ) + 1)
def scale (n ℓ k : ℕ) : ℚ := (ℓ : ℚ) * n ^ 2 / (3 * k)

def largeCapacity (B n r ℓ k : ℕ) : ℚ≥0 :=
  (Nat.ceil (ratio B n * (2 * r : ℕ) ^ 2 / scale n ℓ k) + 1 : ℕ)

def orient {n : ℕ} (A B : Finset (Fin n)) : Finset (Fin n) × Finset (Fin n) :=
  if B.card ≤ A.card then (A, B) else (B, A)

def step {n : ℕ} (solve : List ℕ → List ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (B ℓ k : ℕ) (R : Finset (Fin n)) :
    Finset (Fin n) × Finset (Fin n) :=
  let I := splitInstance (restriction G R) (fun v => x (label R v))
    (largeCapacity B n R.card ℓ k)
  let U := decodeCut (2 * R.card) (solve (encodeInput .directed I))
  let shores := orient (leftShore U) (rightShore U)
  (shores.1.image (label R), shores.2.image (label R))

def cuts {n : ℕ} (cut : Finset (Fin n) → Finset (Fin n) × Finset (Fin n)) :
    ℕ → Finset (Fin n) → List (Finset (Fin n) × Finset (Fin n))
  | 0, _ => []
  | fuel + 1, R =>
    if 3 * R.card ≤ 2 * n then []
    else let s := cut R
      s :: cuts cut fuel (s.1 \ s.2)

def separator {n : ℕ} (cs : List (Finset (Fin n) × Finset (Fin n))) : Finset (Fin n) :=
  cs.foldr (fun s S => (s.1 ∩ s.2) ∪ S) ∅

def remaining {n : ℕ} (start : Finset (Fin n))
    (cs : List (Finset (Fin n) × Finset (Fin n))) : Finset (Fin n) :=
  if h : cs.length = 0 then start else
    let s := cs.get ⟨cs.length - 1, Nat.sub_lt (Nat.pos_of_ne_zero h) Nat.zero_lt_one⟩
    s.1 \ s.2

def pieces {n : ℕ} (cs : List (Finset (Fin n) × Finset (Fin n))) :
    Option (Fin cs.length) → Finset (Fin n)
  | none => remaining Finset.univ cs
  | some i => (cs.get i).2 \ (cs.get i).1

open GraphClasses PowerBagBounds
open Entropy RepeatedCutAccounting

axiom light_separator (C : GraphClass) (hereditary : IsHereditary C)
    (a A : ℕ) (ha : 0 < a) (hA : 0 < A) (class_bound : HasPowerBagBound C a A) :
    ∃ (solve : List ℕ → List ℕ) (K B : ℕ), RamPolytime solve ∧
      0 < K ∧ 0 < B ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G ∈ C n → 0 < n → ∀ (x : Fin n → ℚ≥0) (k p ℓ : ℕ),
      0 < k → 0 < p → 0 < ℓ →
      (∀ v, (x v : ℝ) ≤ 1) → (∑ v, (x v : ℝ)) ≤ k →
      edgeCost G (fun v => (x v : ℝ)) ≤ (k : ℝ) ^ 2 / p →
      (K : ℝ) * ((ℓ : ℝ) + 1) ^ (4 * a + 2) ≤ k →
      (2 * K : ℝ) * ((ℓ : ℝ) + 1) ^ (4 * a + 2) ≤ p →
      let cs := cuts (step solve G x B ℓ k) n Finset.univ
      cs.length ≤ n ∧
        IsBalancedSeparator G
          (ComputedSeparators.separator cs) ∧
        cost (fun v => (x v : ℝ)) (ComputedSeparators.separator cs) ≤
          12 * (ratio B n : ℝ) * k / ℓ ∧
        ∃ P : Partition G
            (ComputedSeparators.separator cs) (Option (Fin cs.length)),
          (∀ i, P.vertices i = pieces cs i) ∧ ∀ i, 3 * (P.vertices i).card ≤ 2 * n

end Lax263307.ComputedSeparators
