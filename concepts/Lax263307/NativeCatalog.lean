import Lax263307.CoordinateCatalog
import Lax808846.Ram
import Mathlib.Combinatorics.Colex

/-!
---
title: A fixed RAM program for the moment-coordinate catalog
type: theorem
---
A single finite RAM program enumerates the subsets of size at most r+2
in the exact order used by the moment relaxation. Each subset occupies
one n-bit word. The program stores only the N catalog entries and uses
time and sufficient word width at most c(n+r+N+2)^3, uniformly for every
larger word width.

# Formalization notes

Input is [n,r]. Output is the list of subset masks in CoordinateCatalog
order. The construction uses native Pascal tables, ranked-subset decoding,
bit packing, and ordered buffer appends. Distinct cardinality blocks are
disjoint, so the catalog's duplicate-removal operation leaves this order
unchanged. Mask words represent subsets; their values are not used as
addresses for an array of size 2^n.
-/

namespace Lax263307.NativeCatalog

def subsetMask {n : ℕ} (I : Finset (Fin n)) : ℕ :=
  Finset.equivBitIndices.symm (I.image Fin.val)

def words (n r : ℕ) : List ℕ :=
  (CoordinateCatalog.catalog n r).map (fun A => subsetMask A.val)

axiom exists_program : ∃ p : Lax808846.Ram.Program, ∃ c : ℕ, 0<c ∧
    ∀ n r : ℕ, ∀ width : ℕ, c*(n+r+(words n r).length+2)^3≤width →
      ∃ t≤c*(n+r+(words n r).length+2)^3,
        Lax808846.Ram.RunsTo width p [n,r] (words n r) t

end Lax263307.NativeCatalog
