import Lax263307.MomentLP
import Lax808846.Ram
import Lax109476.RationalEncoding

/-!
---
title: Input encoding for the moment linear program
type: definition
---
The input to the moment-LP constructor records the graph order, the
independent-set target, the relaxation level, and the adjacency matrix.

# Formalization notes

The first four words are $n$, $k$, $r$, and $n^2$. They are followed by the
adjacency bits in row-major order. This encoding is used by the concrete
RAM constructor in the proof package.
-/

namespace Lax263307.NativeMomentLP

def encodeInput {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ) : List ℕ :=
  n::k::r::(n*n)::(List.ofFn fun u => List.ofFn fun v => if G.Adj u v then 1 else 0).flatten

end Lax263307.NativeMomentLP
