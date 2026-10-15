import Lax263307.EdgeSublinearSeparators
import Lax263307.QPTAS

/-!
---
title: QPTAS for maximum-weight independent set
type: theorem
---
Let $\mathcal C$ be a hereditary graph class with strongly edge-sublinear
separators. Then maximum-weight independent set admits a deterministic
quasipolynomial-time approximation scheme on $\mathcal C$.

For every $G\in\mathcal C$ and rational $0<\varepsilon<1$, it computes
an independent set $I$ with $w(I)\ge(1-\varepsilon)\alpha_w(G)$ in time
$$\exp\!\left((\varepsilon^{-1}\log(n+2))^{O_{\mathcal C}(1)}\right)
  +(\ell+1)^{O_{\mathcal C}(1)}.$$
Here $n=|V(G)|$, $\alpha_w(G)$ is the maximum independent-set weight,
and $\ell$ is the binary encoding length of the rational weights and accuracy.
No separator or algorithm for finding one is part of the input.

# Attribution

Édouard Bonnet and Yeonsu Chang, *QPTAS for Max Weight Independent Set
in Graphs with Strongly Edge-Sublinear Separators*, Theorem 2.

# Formalization notes

The conclusion `HasQPTAS C` is the single predicate defined in `QPTAS`.
It includes one fixed RAM program, its approximation guarantee, and the
uniform bound defined in `QPTASRuntime`. The separator hypothesis uses
the $m+1$ normalization explained in `EdgeSublinearSeparators`.
-/

namespace Lax263307.MainTheorem

open GraphClasses EdgeSublinearSeparators QPTAS

/-- Theorem 2: the deterministic weighted approximation scheme. -/
axiom exists_qptas (C : GraphClass) (hereditary : IsHereditary C)
    (separators : HasStronglyEdgeSublinearSeparators C) : HasQPTAS C

end Lax263307.MainTheorem
