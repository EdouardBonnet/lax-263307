import Lax263307.CoordinateCatalog
import Lax808846.Ram
import Mathlib.Combinatorics.Colex

/-!
---
title: Encoding the moment-coordinate catalogue
type: definition
---
The moment-coordinate catalogue lists subsets of the vertex set in the
order used by the relaxation. Each subset is represented by its binary
membership mask; `words` is the resulting list of masks.

# Formalization notes

Masks encode subsets of `Fin n`. The catalogue contains only the subsets
needed by the relaxation, rather than an array indexed by all $2^n$ masks.
-/

namespace Lax263307.NativeCatalog

open CoordinateCatalog (catalog)
def subsetMask {n : ℕ} (I : Finset (Fin n)) : ℕ :=
  Finset.equivBitIndices.symm (I.image Fin.val)

def words (n r : ℕ) : List ℕ :=
  (catalog n r).map (fun A => subsetMask A.val)

end Lax263307.NativeCatalog
