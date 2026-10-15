import Lax263307.Entropy

/-!
---
title: Entropy lies between zero and the logarithm of the order
type: lemma
---
For every probability vector on $n$ vertices,
$$0\le H(\pi)\le\log_2 n.$$

# Attribution

Bonnet–Chang, proof of Lemma 12. The upper bound follows from concavity
of $-x\log x$, with equality at the uniform distribution.
-/

namespace Lax263307.EntropyBounds

open Entropy

/-- The entropy bounds used to limit successive conditioning steps. -/
axiom entropy_bounds {n : ℕ} (π : Fin n → ℝ) (probability : IsProbability π) :
    0 ≤ entropy π ∧ entropy π ≤ Real.logb 2 n

end Lax263307.EntropyBounds
