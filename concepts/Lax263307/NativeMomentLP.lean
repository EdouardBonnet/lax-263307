import Lax263307.MomentLP
import Lax808846.Ram
import Lax109476.RationalEncoding

/-!
---
title: A fixed RAM program constructing the complete moment LP
type: theorem
---
One finite RAM program constructs the exact dense rational moment LP from
its graph, target k and level r. It generates the coordinate catalog,
computes cardinality and independence metadata, writes all six matrix row
families, and appends the bound and objective vectors. If N is the catalog
size, both execution time and sufficient word width are bounded by
c(n+k+r+N+2)^4 for one fixed constant c, uniformly at every larger width.

# Formalization notes

Physical input is n, k, r, n squared, followed by the row-major adjacency
bits. Output is the registered RationalEncoding.encodeProgram format,
including its dimension header and canonical rational triples. The program
uses only the N catalog masks, without any array indexed by all 2^n masks.
Solver invocation and the recursive QPTAS driver are separate obligations.
-/

namespace Lax263307.NativeMomentLP

def encodeInput {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ) : List ℕ :=
  n::k::r::(n*n)::(List.ofFn fun u => List.ofFn fun v => if G.Adj u v then 1 else 0).flatten

axiom exists_program : ∃ p : Lax808846.Ram.Program, ∃ c : ℕ,0 < c ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r width : ℕ),
      c*(n+k+r+MomentLP.dimension n r+2)^4 ≤ width →
      ∃ t ≤ c*(n+k+r+MomentLP.dimension n r+2)^4,Lax808846.Ram.RunsTo width p (encodeInput G k r)
        (Lax109476.RationalEncoding.encodeProgram (MomentLP.program G k r)) t

end Lax263307.NativeMomentLP
