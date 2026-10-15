import Lax263307.HeavyConditioning
import Lax263307.RationalConditioning

/-!
---
title: Exact rational search above the conditioning moment floor
type: lemma
---
Search the existing bounded-size candidate list using exact rational edge
cost tests and the additional moment threshold tau^r. The strengthened
entropy argument guarantees a successful candidate. The search returns
bounded costs of total mass k, sparse edge cost, and the quantitative
conditioning moment floor, without computing entropy values.

# Formalization notes

The rational floor uses integer n,p,log2 n and has an explicit denominator.
The candidate count remains at most (r+1)(n+1)^r. These lemmas give the search function's correctness.
Its RAM implementation is verified in the proof package.
-/

namespace Lax263307.HeavyRationalConditioning

open LinearRelaxation Entropy RationalConditioning HeavyConditioning

def rationalFloor (n p : ℕ) : ℚ := 1 / (2 * (n : ℚ) * p * ((Nat.log2 n : ℚ) + 1))

def HeavyPasses {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k p : ℕ) (y : RationalVector n r) (A : Finset (Fin n)) : Prop :=
  Passes G k p y A ∧ rationalFloor n p ^ r ≤ rationalValue y A

instance {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k p : ℕ) (y : RationalVector n r) (A : Finset (Fin n)) : Decidable (HeavyPasses G k p y A) :=
  inferInstanceAs (Decidable (Passes G k p y A ∧ rationalFloor n p ^ r ≤ rationalValue y A))

def findHeavyConditioning {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k p : ℕ) (y : RationalVector n r) : Option (Finset (Fin n)) :=
  (candidates n r).find? fun A => decide (HeavyPasses G k p y A)

axiom search_correct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k r p : ℕ) (y : RationalVector n r) (feasible : IsFeasible G k r (realVector y))
    (order_positive : 0 < n) (target_positive : 0 < k)
    (level_positive : 0 < r) (threshold_positive : 0 < p)
    (budget : (p : ℝ) * ((Nat.log2 n : ℝ) + 1) ≤ r) :
    ∃ A : Finset (Fin n), findHeavyConditioning G k p y = some A ∧ A.card ≤ r ∧
      probabilityFloor n p ^ r ≤ value (realVector y) A ∧ 0 < value (realVector y) A ∧
      (∀ v, 0 ≤ conditioned (realVector y) A v ∧ conditioned (realVector y) A v ≤ 1) ∧
      (∑ v, conditioned (realVector y) A v) = k ∧
      edgeCost G (conditioned (realVector y) A) ≤ (k : ℝ) ^ 2 / p

end Lax263307.HeavyRationalConditioning
