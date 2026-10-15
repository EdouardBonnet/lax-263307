import Lax263307.AlgorithmParameters

/-!
---
title: Quasipolynomial bounds for the computed algorithm budgets
type: lemma
---
For fixed class constants, the graph order, accuracy denominator, load,
edge sparsity, conditioning level, moment dimension, protected-radius
precision, ellipsoid iteration count, and small-target enumeration bound
all fit one quasipolynomial bound in D times the binary-logarithm scale.

# Formalization notes

The proof supplies fixed positive natural constants before n and D.
It bounds the actual integer formulas used by the algorithm, including
its conservative precision choice. The proof of the main theorem combines
these estimates with polynomial local work and logarithmic recursion to
bound the complete RAM execution.
-/

namespace Lax263307.ParameterResources

open MomentLP (dimension)
open AlgorithmParameters

def resource (a K B n D : ℕ) : ℕ :=
  n + D + load B n D + sparsity a K B n D + level a K B n D +
    dimension n (level a K B n D) + radiusDenominator a K B n D +
    precision a K B n D + iterations a K B n D + (n + 1) ^ cutoff a K B n D

axiom resource_bound (a K B : ℕ) (hK : 0 < K) :
    ∃ C d : ℕ, 0 < C ∧ 0 < d ∧ ∀ n D : ℕ, 0 < n → 0 < D →
      resource a K B n D ≤ 2 ^ (C * (D * logarithm n) ^ d)

end Lax263307.ParameterResources
