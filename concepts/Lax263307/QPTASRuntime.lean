import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Log

/-!
---
title: The quasipolynomial approximation bound
type: definition
---
For fixed positive integers $c,d$, the running-time bound is
$$2^{c(\lceil1/\varepsilon\rceil(1+\lfloor\log_2(n+2)\rfloor))^d}
  +c(\ell+1)^d.$$
Here $n$ is the graph order, $\varepsilon$ is the requested accuracy, and
$\ell$ is the binary length of the rational weights and accuracy.

# Formalization notes

The natural-number formula includes small and empty graphs. The constants
are fixed for the graph class before the input is supplied. Polynomial
overheads can be absorbed by increasing them, while preserving the
additive polynomial dependence on $\ell$.
-/

namespace Lax263307.QPTASRuntime

/-- The stronger internal time and sufficient word-width bound for the source algorithm. -/
def timeBound (c d n ℓ : ℕ) (ε : ℚ) : ℕ :=
  2 ^ (c * (⌈ε⁻¹⌉₊ * (Nat.log2 (n + 2) + 1)) ^ d) + c * (ℓ + 1) ^ d

end Lax263307.QPTASRuntime
