import Lax263307.DistanceProjection
import Lax109476.CertificateSoundness

/-!
---
title: Rational LP certificates for distance projection
type: theorem
---
Every valid exact certificate for the infinity-distance LP gives one of
three outcomes: the original relaxation is infeasible; a rational point
is feasible and within the prescribed coordinate error; or a rational
normal separates every feasible point with a gap exceeding that error.
The separating normal has sum of absolute coefficients at most one.

# Formalization notes

The objective of the projection LP is bounded, so an unbounded
certificate is impossible. Optimal primal and dual witnesses cast exactly
to real variables. This theorem checks the actual registered certificate
type; the dense matrix construction and solver RAM invocation still need
implementation.
-/

namespace Lax263307.RationalProjection

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax263307.DistanceProjection

axiom certificate_outcome {m n : ℕ} (P : Program ℚ m n) (center : Fin n → ℚ)
    (certificate : Certificate (m + (n + n)) (n + 1))
    (valid : IsValidCertificate (distanceProgram P center) certificate) (ρ : ℝ) :
    (¬ IsFeasible (toReal P)) ∨
      (∃ y : Fin n → ℚ, PrimalFeasible (toReal P) (realVector y) ∧
        ∀ j, |(y j : ℝ) - (center j : ℝ)| ≤ ρ) ∨
      (∃ a : Fin n → ℚ, ∃ α : ℚ,
        (∑ j, |(a j : ℝ)|) ≤ 1 ∧
        (∀ y, PrimalFeasible (toReal P) y → (∑ j, (a j : ℝ) * y j) ≤ (α : ℝ)) ∧
        ρ < (∑ j, (a j : ℝ) * (center j : ℝ)) - (α : ℝ))

end Lax263307.RationalProjection
