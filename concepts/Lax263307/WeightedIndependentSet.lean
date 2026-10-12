import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Rat.Floor
import Lax759944.BinaryWordEncoding

/-!
---
title: Maximum-weight independent set and its encoding
type: definition
---
Given a graph $G$ with rational vertex weights $w$, maximum-weight
independent set asks for an independent set of maximum total weight.
An $(1-\varepsilon)$-approximation is an independent set $I$ with
$w(I)\ge(1-\varepsilon)w(J)$ for every independent set $J$.

The input consists of the number of vertices, the adjacency matrix,
the vertex weights, and the requested rational accuracy. The output
is the membership vector of the returned independent set.

# Formalization notes

The comparison with every independent set avoids choosing an optimum.
Weights may be negative: such vertices can be discarded, as can zero-weight
vertices, so this includes the nonnegative case used in Section 6.
Each rational is encoded by the sign of its reduced numerator, its absolute
numerator, and its positive denominator. The sign is zero for nonnegative
numbers and one for negative numbers. All matrix and vector entries are in
vertex order. The rational encoding length $\ell$ includes the weights and
$\varepsilon$, and is measured by the registered binary word encoding.
-/

namespace Lax263307.WeightedIndependentSet

/-- Total weight of a vertex set. -/
def weight {n : ℕ} (w : Fin n → ℚ) (I : Finset (Fin n)) : ℚ :=
  ∑ v ∈ I, w v

/-- An independent set that achieves the requested multiplicative guarantee. -/
def IsApproximation {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ)
    (ε : ℚ) (I : Finset (Fin n)) : Prop :=
  G.IsIndepSet (I : Set (Fin n)) ∧
    ∀ J : Finset (Fin n), G.IsIndepSet (J : Set (Fin n)) →
      (1 - ε) * weight w J ≤ weight w I

/-- Canonical sign, absolute numerator, and denominator of a rational. -/
def encodeRational (q : ℚ) : List ℕ :=
  [if q.num < 0 then 1 else 0, q.num.natAbs, q.den]

/-- The rational parameters in vertex order, followed by the accuracy. -/
def encodeParameters {n : ℕ} (w : Fin n → ℚ) (ε : ℚ) : List ℕ :=
  (List.ofFn w).flatMap encodeRational ++ encodeRational ε

/-- Total binary encoding length of the weights and the accuracy. -/
def rationalBitSize {n : ℕ} (w : Fin n → ℚ) (ε : ℚ) : ℕ :=
  Lax759944.BinaryWordEncoding.bitSize (encodeParameters w ε)

/-- The full input word, including the row-major adjacency matrix. -/
def encodeInput {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Fin n → ℚ) (ε : ℚ) : List ℕ :=
  [n] ++ (List.ofFn fun u => List.ofFn fun v =>
    if G.Adj u v then 1 else 0).flatten ++ encodeParameters w ε

/-- The length-`n` membership vector of the selected independent set. -/
def encodeOutput {n : ℕ} (I : Finset (Fin n)) : List ℕ :=
  List.ofFn fun v => if v ∈ I then 1 else 0

end Lax263307.WeightedIndependentSet
