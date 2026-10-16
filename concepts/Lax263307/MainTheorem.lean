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

For every $G\in\mathcal C$ and integer precision $k>0$, one fixed program
computes an independent set of weight at least $\alpha_w(G)/(1+1/k)$.
Its running time, for each fixed $k$, is quasipolynomial in the binary size
of the structurally encoded graph and rational weights, as specified by
the registered `QPTAS` definition in lax-213208.
No separator or algorithm for finding one is part of the input.

# Attribution

Édouard Bonnet and Yeonsu Chang, *QPTAS for Max Weight Independent Set
in Graphs with Strongly Edge-Sublinear Separators*, Theorem 2.

# Formalization notes

The conclusion `HasQPTAS C` specializes lax-213208's `QPTAS` to the MWIS
problem. The structured algorithm uses accuracy $\varepsilon=1/(k+1)$;
its checked source bound is
$$\exp\!\left((\varepsilon^{-1}\log(n+2))^{O_{\mathcal C}(1)}\right)
  +(\ell+1)^{O_{\mathcal C}(1)},$$
where $\ell$ measures the rational parameters. The proof absorbs the structural
reader and compiler costs into the archive's quasipolynomial envelope, and
uses lax-62's high-level compilation theorem directly. The separator hypothesis
uses the $m+1$ normalization explained in `EdgeSublinearSeparators`.
-/

namespace Lax263307.MainTheorem

open GraphClasses EdgeSublinearSeparators QPTAS

/-- Theorem 2: the deterministic weighted approximation scheme. -/
axiom exists_qptas (C : GraphClass) (hereditary : IsHereditary C)
    (separators : HasStronglyEdgeSublinearSeparators C) : HasQPTAS C

end Lax263307.MainTheorem
