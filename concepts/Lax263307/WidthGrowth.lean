import Mathlib.Data.Nat.Basic

/-!
---
title: Polynomial order bound from the sampled width inequality
type: lemma
---
Suppose $W(m)^a\le A(m+1)^{a-1}$ and $W(m)\ge1$. For a source graph of
order $t$ and at most $2t$ edges, take route cutoff $24c\ell$. If its linear
width lower bound and discarded-route estimate are both compatible with
the sampled width upper bound, then
$t\le (12c)^a A(6(24c)^2+1)^{a-1}\ell^{2(a-1)}$.
This integer inequality makes the sampling contradiction polynomial in ell.
-/

namespace Lax263307.WidthGrowth

def threshold (a A c : ℕ) : ℕ := (12 * c) ^ a * A * (6 * (24 * c) ^ 2 + 1) ^ (a - 1)

axiom order_bound (a A c ℓ t m q : ℕ) (a_positive : 0 < a) (ℓ_positive : 0 < ℓ)
    (t_positive : 0 < t) (W : ℕ → ℕ)
    (W_positive : ∀ M, 1 ≤ W M) (W_power : ∀ M, (W M) ^ a ≤ A * (M + 1) ^ (a - 1))
    (edges : m ≤ 2 * t) (discarded : (24 * c * ℓ) * q ≤ 4 * m * ℓ)
    (width : t ≤ c * (max 1 (6 * W (3 * m * (24 * c * ℓ) ^ 2)) + q)) :
    t ≤ threshold a A c * ℓ ^ (2 * (a - 1))

end Lax263307.WidthGrowth
