import Lax263307.IndependentBlowUp
import Mathlib.Data.Finset.Max

/-!
---
title: Scaling weights to integer multiplicities
type: definition
---
For nonnegative rational vertex weights, let $W$ be the maximum weight and
choose $\tau=\varepsilon W/(2n)$. The rounded multiplicity of vertex $v$ is
$t_v=\lfloor w_v/\tau\rfloor$. Vertices with $t_v=0$ are omitted from the
independent blow-up.

# Formalization notes

The maximum includes zero, so it is defined also on the empty graph and on
signed weights before preprocessing. The rounding estimates assume
$n>0$, $W>0$, and $\varepsilon>0$, ensuring $\tau>0$.
The natural-valued floor is computed on exact rational numbers.
-/

namespace Lax263307.WeightRounding

/-- The maximum of the vertex weights and zero. -/
def maximumWeight {n : ℕ} (w : Fin n → ℚ) : ℚ :=
  (insert 0 (Finset.univ.image w)).max' (Finset.insert_nonempty _ _)

/-- The weight unit used by the reduction. -/
def scale {n : ℕ} (w : Fin n → ℚ) (ε : ℚ) : ℚ :=
  ε * maximumWeight w / (2 * n)

/-- Multiplicities at a specified positive weight unit. -/
def roundedCopies {n : ℕ} (w : Fin n → ℚ) (τ : ℚ) : Fin n → ℕ :=
  fun v => ⌊w v / τ⌋₊

/-- The multiplicities chosen for the requested accuracy. -/
def copies {n : ℕ} (w : Fin n → ℚ) (ε : ℚ) : Fin n → ℕ :=
  roundedCopies w (scale w ε)

end Lax263307.WeightRounding
