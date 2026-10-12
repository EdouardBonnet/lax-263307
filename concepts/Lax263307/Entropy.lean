import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
---
title: Entropy and adjacency mass
type: definition
---
For a probability vector $\pi$ on $n$ vertices, its entropy in bits is
$$H(\pi)=-\sum_v\pi_v\log_2\pi_v,$$
with zero summands at zero probabilities. Its adjacency mass in a graph $G$ is
$$\sum_{u,v:\,uv\in E(G)}\pi_u\pi_v,$$
where ordered adjacent pairs are counted, so each edge contributes twice.

# Formalization notes

The auxiliary natural-log entropy differs by the positive factor $\ln2$.
Both definitions use mathlib's `negMulLog`, whose value at zero is zero.
The adjacency mass is an ordered sum, avoiding choices of edge orientations.
-/

namespace Lax263307.Entropy

/-- A nonnegative vector with total mass one. -/
def IsProbability {n : ℕ} (π : Fin n → ℝ) : Prop :=
  (∀ v, 0 ≤ π v) ∧ (∑ v, π v) = 1

/-- Entropy measured with natural logarithms. -/
noncomputable def naturalEntropy {n : ℕ} (π : Fin n → ℝ) : ℝ :=
  ∑ v, Real.negMulLog (π v)

/-- Shannon entropy in bits. -/
noncomputable def entropy {n : ℕ} (π : Fin n → ℝ) : ℝ :=
  naturalEntropy π / Real.log 2

/-- Total product probability of ordered adjacent vertex pairs. -/
noncomputable def adjacencyMass {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (π : Fin n → ℝ) : ℝ :=
  ∑ u, ∑ v, if G.Adj u v then π u * π v else 0

/-- Sum of endpoint-cost products over unordered edges. -/
noncomputable def edgeCost {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (x : Fin n → ℝ) : ℝ :=
  adjacencyMass G x / 2

end Lax263307.Entropy
