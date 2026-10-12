import Lax263307.EntropyBounds
import Lax263307Proofs.EntropyAlgebra

namespace Lax263307Proofs.EntropyBounds

open Lax263307.Entropy EntropyAlgebra

/--
---
conclusion: Lax263307.EntropyBounds.entropy_bounds
---
The entropy of a probability vector lies between zero and the logarithm
of the number of vertices.

# Proof strategy

Each entropy summand is nonnegative. Jensen's inequality for the concave
function `negMulLog` bounds their sum by the entropy of the uniform vector.
Divide by the positive logarithm of two to obtain the bound in bits.

# Attribution

Bonnet–Chang, proof of Lemma 12.
-/
theorem entropy_bounds {n : ℕ} (π : Fin n → ℝ) (probability : IsProbability π) :
    0 ≤ entropy π ∧ entropy π ≤ Real.logb 2 n := by
  constructor
  · exact div_nonneg (natural_entropy_nonneg π probability) log_two_pos.le
  · exact div_le_div_of_nonneg_right (natural_entropy_le_log π probability) log_two_pos.le

end Lax263307Proofs.EntropyBounds
