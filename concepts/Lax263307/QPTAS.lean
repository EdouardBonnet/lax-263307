import Lax263307.GraphClasses
import Lax263307.WeightedIndependentSet
import Lax808846.Ram
import Mathlib.Data.Nat.Log

/-!
---
title: Deterministic quasipolynomial-time approximation schemes
type: definition
---
A deterministic QPTAS for maximum-weight independent set on a class
$\mathcal C$ uses one finite program, depending only on $\mathcal C$,
which returns a $(1-\varepsilon)$-approximation on every member with
rational weights and rational $0<\varepsilon<1$.
Its running time has the form
$$2^{(\varepsilon^{-1}\log(n+2))^{O_{\mathcal C}(1)}}
  +(\ell+1)^{O_{\mathcal C}(1)},$$
where $\ell$ is the binary length of the weights and accuracy.
Neither class recognition nor a separator is supplied as input.

# Formalization notes

Execution is `Lax808846.Ram.RunsTo` on the registered word RAM.
The supplied input is exactly `encodeInput`, with no implicit length prefix.
The constants and program precede the input and word width in the quantifiers.
The natural-number time bound uses $\lceil1/\varepsilon\rceil$ and
$1+\lfloor\log_2(n+2)\rfloor$ to cover small inputs.

The same bound is a sufficient word width, and the program must work at
every larger width. In particular it works at that explicitly prescribed
width; there is no advice hidden in a choice of width. Allowing this many
bits accommodates exact rational subroutines. Simulating these bounded-word
operations with bit operations costs a polynomial in the time bound,
which remains of the displayed form after increasing its constants and
exponent: $(A+B)^k\le2^{k-1}(A^k+B^k)$. Thus the additive polynomial
dependence on $\ell$ is preserved. Correctness and time are promised only
on well-formed inputs whose graphs belong to $\mathcal C$.
-/

namespace Lax263307.QPTAS

open GraphClasses WeightedIndependentSet Lax808846.Ram

/-- An explicit bound representing the paper's two-parameter running time. -/
def timeBound (c d n ℓ : ℕ) (ε : ℚ) : ℕ :=
  2 ^ (c * (⌈ε⁻¹⌉₊ * (Nat.log2 (n + 2) + 1)) ^ d) + c * (ℓ + 1) ^ d

/-- One uniform deterministic word-RAM program realizes the approximation scheme. -/
def HasQPTAS (C : GraphClass) : Prop :=
  ∃ (program : Program) (c d : ℕ), 0 < c ∧ 0 < d ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G ∈ C n → ∀ (weights : Fin n → ℚ) (ε : ℚ), 0 < ε → ε < 1 →
        let T := timeBound c d n (rationalBitSize weights ε) ε
        ∀ wordLength : ℕ, T ≤ wordLength →
          ∃ I : Finset (Fin n), IsApproximation G weights ε I ∧
            ∃ t ≤ T, RunsTo wordLength program
              (encodeInput G weights ε) (encodeOutput I) t

end Lax263307.QPTAS
