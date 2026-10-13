import Lax263307.InducedEmbeddingWidth
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

/-!
---
title: Integer power bounds on class decomposition bags
type: theorem
---
A uniform bound $|B|^a\le A(m+1)^{a-1}$ gives the monotone bag-size function
$W(m)=\lfloor\sqrt[a]{A(m+1)^{a-1}}\rfloor$. For $a,A>0$, this function
is at least one and obeys the same power bound. Integer powers suffice for
the sampled width contradiction once separators yield such a class bound.

# Attribution

An integer form of the sublinear width bound used in Bonnet–Chang's Lemma 11.
-/

namespace Lax263307.PowerBagBounds

open Lax263307.GraphClasses Lax263307.InducedEmbeddingWidth Lax228581.Treewidth

def HasPowerBagBound (C : GraphClass) (a A : ℕ) : Prop :=
  ∀ n (G : SimpleGraph (Fin n)), G ∈ C n → ∃ D : TreeDecomposition G,
    ∀ i, (D.bag i).card ^ a ≤ A * (G.edgeSet.ncard + 1) ^ (a - 1)

def bagBound (a A m : ℕ) : ℕ := Nat.nthRoot a (A * (m + 1) ^ (a - 1))

axiom root_bag_bound (C : GraphClass) (a A : ℕ) (a_positive : 0 < a) (A_positive : 0 < A)
    (class_bound : HasPowerBagBound C a A) :
    Monotone (bagBound a A) ∧ HasBagBound C (bagBound a A) ∧
      (∀ m, 1 ≤ bagBound a A m) ∧
      (∀ m, (bagBound a A m) ^ a ≤ A * (m + 1) ^ (a - 1))

end Lax263307.PowerBagBounds
