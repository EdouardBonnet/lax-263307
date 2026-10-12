import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Real.Basic

/-!
---
title: The independent-set relaxation and its exact hull
type: definition
---
For an $n$-vertex graph $G$, target $k$, and level $r$, the relaxation
$R_r(G,k)$ has coordinates $y_A$ for vertex sets $|A|\le r+2$ and constraints
$$y_\varnothing=1,\qquad 0\le y_A\le1,$$
$$y_{A\cup\{v\}}\le y_A\quad (|A|\le r+1),$$
$$y_A=0\quad\text{if }A\text{ is not independent},$$
$$\sum_v y_{A\cup\{v\}}=k y_A\quad (|A|\le r+1).$$
The exact hull $P_r(G,k)$ is the convex hull of the vectors
$y_A=\mathbf1[A\subseteq I]$ over independent sets $I$ of size $k$.
For $y_A>0$, conditioning on $A$ gives costs $x_v=y_{A\cup\{v\}}/y_A$.

# Formalization notes

The coordinate type contains exactly the sets of size at most $r+2$;
there are no coordinates for larger sets. The accessor is extended by zero
outside this domain, solely to simplify notation. Every constraint that
uses it supplies a size bound ensuring that it reads an actual coordinate.
The vector space and convex hull are over the reals, as in the paper;
the algorithms will use rational points in this space.
-/

namespace Lax263307.LinearRelaxation

/-- The coordinate sets of the level-`r` relaxation. -/
abbrev Coordinate (n r : ℕ) := {A : Finset (Fin n) // A.card ≤ r + 2}

/-- A vector with precisely the coordinates used by the relaxation. -/
abbrev MomentVector (n r : ℕ) := Coordinate n r → ℝ

/-- Read a coordinate, returning zero outside the truncated coordinate domain. -/
def value {n r : ℕ} (y : MomentVector n r) (A : Finset (Fin n)) : ℝ :=
  if h : A.card ≤ r + 2 then y ⟨A, h⟩ else 0

/-- The indicator encoding of a vertex set. -/
def indicator {n : ℕ} (r : ℕ) (I : Finset (Fin n)) : MomentVector n r :=
  fun A => if A.val ⊆ I then 1 else 0

/-- The five families of linear constraints defining `R_r(G,k)`. -/
structure IsFeasible {n : ℕ} (G : SimpleGraph (Fin n)) (k r : ℕ)
    (y : MomentVector n r) : Prop where
  /-- The empty moment is normalized. -/
  normalized : value y ∅ = 1
  /-- Each moment lies in the unit interval. -/
  bounds : ∀ A, 0 ≤ y A ∧ y A ≤ 1
  /-- Adding a vertex cannot increase a moment. -/
  monotone : ∀ A : Finset (Fin n), A.card ≤ r + 1 →
    ∀ v, value y (insert v A) ≤ value y A
  /-- Nonindependent sets have zero moment. -/
  vanishes : ∀ A : Coordinate n r, ¬G.IsIndepSet (A.val : Set (Fin n)) → y A = 0
  /-- The cardinality constraint remains valid after conditioning. -/
  mass : ∀ A : Finset (Fin n), A.card ≤ r + 1 →
    ∑ v : Fin n, value y (insert v A) = (k : ℝ) * value y A

/-- The convex hull of encodings of size-`k` independent sets. -/
def independentSetHull {n : ℕ} (G : SimpleGraph (Fin n)) (k r : ℕ) :
    Set (MomentVector n r) :=
  convexHull ℝ {y | ∃ I : Finset (Fin n),
    G.IsIndepSet (I : Set (Fin n)) ∧ I.card = k ∧ y = indicator r I}

/-- Vertex costs after conditioning on inclusion of `A`. -/
noncomputable def conditioned {n r : ℕ} (y : MomentVector n r)
    (A : Finset (Fin n)) (v : Fin n) : ℝ :=
  value y (insert v A) / value y A

/-- A certified upper bound on independent sets contained in a vertex set. -/
def IsIndependenceBound {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Finset (Fin n)) (u : ℕ) : Prop :=
  ∀ J : Finset (Fin n), J ⊆ C → G.IsIndepSet (J : Set (Fin n)) → J.card ≤ u

end Lax263307.LinearRelaxation
