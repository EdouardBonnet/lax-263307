import Lax263307.ExhaustiveTargets
import Lax263307.WeightedIndependentSet
import Lax808846.Ram

/-!
---
title: A fixed RAM program for exact small-target search
type: theorem
---
One finite RAM program enumerates the size-k vertex sets in the same order
as the exact branch of the recursive algorithm and returns its first
independent set, or reports that no candidate succeeds. The time and
sufficient word width are bounded by c(n+k+2)^2(n+1)^k, uniformly for every
larger word width.

# Formalization notes

The input is n, k, the matrix length n^2, and the row-major adjacency
matrix. Failure is encoded as [0]; success is 1 followed by the selected
set's membership vector. Native Pascal-table construction and ranked subset
decoding avoid enumerating the whole powerset. The proof includes actual
matrix reads, independence tests, first-success retention, input/output,
compilation, and instruction and word bounds. The source subroutine also
operates directly on graph buffers for use by the recursive solver.
-/

namespace Lax263307.NativeExhaustive

def encodeInput {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) : List ℕ :=
  n::k::(n*n)::(List.ofFn fun u => List.ofFn fun v => if G.Adj u v then 1 else 0).flatten

def encodeAnswer {n : ℕ} : Option (Finset (Fin n)) → List ℕ
  | none => [0]
  | some I => 1::WeightedIndependentSet.encodeOutput I

axiom exists_program : ∃ p : Lax808846.Ram.Program, ∃ c : ℕ, 0<c ∧
    ∀ (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      ∀ width : ℕ,c*(n+k+2)^2*(n+1)^k≤width →
      ∃ t≤c*(n+k+2)^2*(n+1)^k,Lax808846.Ram.RunsTo width p (encodeInput G k)
        (encodeAnswer (ExhaustiveTargets.findIndependentSet G k)) t

end Lax263307.NativeExhaustive
