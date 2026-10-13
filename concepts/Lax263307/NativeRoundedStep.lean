import Lax263307.RoundedOracleSearch
import Lax808846.Ram

/-!
---
title: A uniform RAM program for the rounded ellipsoid update
type: theorem
---
One fixed finite RAM program reads a rational shape, an integer cut normal,
a rational center, and the iteration index, and writes the rounded next
shape and center. Both its instruction count and sufficient word length
are polynomial in the dimension, iteration index, and coordinate bit bound.
It works at every larger word length. The input has no length prefix.

# Formalization notes

This statement concerns actual `Lax808846.Ram.RunsTo`. The proof compiles
the registered LP submission's complete rational ellipsoid update, adding
the input reader and canonical output writer. It is one subroutine of the
recursive QPTAS; it does not assert that the complete QPTAS program exists.
-/

namespace Lax263307.NativeRoundedStep

open Matrix Lax263307.RoundedOracleSearch Lax109476.RationalEncoding

def height (q : ℚ) (h : ℕ) : Prop := q.num.natAbs ≤ 2 ^ h ∧ q.den ≤ 2 ^ h

def encodeInput {n : ℕ} (k : ℕ) (state : State n) (a : Fin n → ℤ) : List ℕ :=
  [n, k] ++ (List.ofFn fun i => encodeVector (state.1 i)).flatten ++
    encodeVector (rationalNormal a) ++ encodeVector state.2

def encodeOutput {n : ℕ} (state : State n) : List ℕ :=
  (List.ofFn fun i : Fin (n * n) => state.1 i.divNat i.modNat).flatMap encodeRational ++
    encodeVector state.2

axiom exists_program : ∃ p : Lax808846.Ram.Program, ∃ c : ℕ, 0 < c ∧
    ∀ (n k h : ℕ), 2 ≤ n → 1 ≤ h →
      ∀ (state : State n) (a : Fin n → ℤ),
        (∀ i j, height (state.1 i j) h) →
        (∀ i, height (rationalNormal a i) h) → (∀ i, height (state.2 i) h) →
        0 < rationalNormal a ⬝ᵥ (state.1 *ᵥ rationalNormal a) →
        ∀ w : ℕ, c * (n + h + k + 1) ^ 12 ≤ w →
          ∃ t ≤ c * (n + h + k + 1) ^ 12, Lax808846.Ram.RunsTo w p
            (encodeInput k state a) (encodeOutput (update k state a)) t

end Lax263307.NativeRoundedStep
