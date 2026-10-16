import Lax263307.PathSampling
import Mathlib.Tactic

namespace Lax263307Proofs.PathSampling

open Lax263307.PathSampling Lax263307.Entropy

theorem load_nonnegative {n q : ℕ} (P : Distribution n q) (v : Fin n) :
    0 ≤ load P v := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact P.nonnegative i
  · exact le_rfl

theorem indicator_product (a b : Prop) [Decidable a] [Decidable b] (x y : ℝ) :
    (if a then x else 0) * (if b then y else 0) = if a ∧ b then x * y else 0 := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb]

theorem swap_inner_sums {a b c : ℕ} (f : Fin a → Fin b → Fin c → ℝ) :
    (∑ i, ∑ j, ∑ v, f i j v) = ∑ v, ∑ i, ∑ j, f i j v := by
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

theorem pair_load_product {n q : ℕ} (P : Distribution n q) (u v : Fin n) :
    (∑ i, ∑ j, if u ∈ P.vertices i ∧ v ∈ P.vertices j then
      P.probability i * P.probability j else 0) = load P u * load P v := by
  unfold load
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact (indicator_product _ _ _ _).symm

/--
---
conclusion: Lax263307.PathSampling.expected_size_identity
---
Count each outcome's vertices by their indicator functions and interchange
the finite sums over vertices and outcomes.
-/
theorem expected_size_identity {n q : ℕ} (P : Distribution n q) :
    expectedSize P = ∑ v, load P v := by
  unfold expectedSize load
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [Finset.sum_ite_mem, mul_comm]

/--
---
conclusion: Lax263307.PathSampling.collision_union_bound
---
If two outcomes intersect, at least one vertex witnesses that event. Sum
the resulting indicator bound against the product outcome probabilities,
interchange the sums, and factor each vertex contribution into the product
of its two identical loads.
-/
theorem collision_union_bound {n q : ℕ} (P : Distribution n q) :
    collisionProbability P ≤ ∑ v, (load P v) ^ 2 := by
  classical
  have hpair (i j : Fin q) :
      (if ¬Disjoint (P.vertices i) (P.vertices j) then P.probability i * P.probability j else 0) ≤
      ∑ v : Fin n, if v ∈ P.vertices i ∧ v ∈ P.vertices j then
        P.probability i * P.probability j else 0 := by
    by_cases h : ¬Disjoint (P.vertices i) (P.vertices j)
    · obtain ⟨v, hvi, hvj⟩ := Finset.not_disjoint_iff.mp h
      rw [if_pos h]
      have hs := Finset.single_le_sum
        (f := fun v : Fin n => if v ∈ P.vertices i ∧ v ∈ P.vertices j then
          P.probability i * P.probability j else 0)
        (fun v _ => by split_ifs <;> first | exact mul_nonneg (P.nonnegative i) (P.nonnegative j) | exact le_rfl)
        (Finset.mem_univ v)
      simpa only [if_pos (And.intro hvi hvj)] using hs
    · rw [if_neg h]
      apply Finset.sum_nonneg
      intro v _
      split_ifs <;> first | exact mul_nonneg (P.nonnegative i) (P.nonnegative j) | exact le_rfl
  calc
    collisionProbability P ≤ ∑ i, ∑ j, ∑ v : Fin n,
        if v ∈ P.vertices i ∧ v ∈ P.vertices j then P.probability i * P.probability j else 0 :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair i j
    _ = ∑ v, ∑ i, ∑ j,
        if v ∈ P.vertices i ∧ v ∈ P.vertices j then P.probability i * P.probability j else 0 :=
      swap_inner_sums _
    _ = ∑ v, (load P v) ^ 2 := by simp_rw [pair_load_product, pow_two]

/--
---
conclusion: Lax263307.PathSampling.adjacency_union_bound
---
An ordered adjacent pair witnesses every edge joining two outcomes. Sum
these witness indicators, then factor the two independent outcome probabilities
into the corresponding endpoint loads. Ordered pairs account for both edge
orientations.
-/
theorem adjacency_union_bound {n q : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (P : Distribution n q) :
    adjacencyProbability G P ≤ adjacencyMass G (load P) := by
  classical
  have hpair (i j : Fin q) :
      (if ∃ u ∈ P.vertices i, ∃ v ∈ P.vertices j, G.Adj u v then
        P.probability i * P.probability j else 0) ≤
      ∑ u : Fin n, ∑ v : Fin n, if G.Adj u v ∧ u ∈ P.vertices i ∧ v ∈ P.vertices j then
        P.probability i * P.probability j else 0 := by
    have hn (u v : Fin n) :
        0 ≤ if G.Adj u v ∧ u ∈ P.vertices i ∧ v ∈ P.vertices j then
          P.probability i * P.probability j else 0 := by
      split_ifs <;> first | exact mul_nonneg (P.nonnegative i) (P.nonnegative j) | exact le_rfl
    split_ifs with h
    · obtain ⟨u, hui, v, hvj, huv⟩ := h
      calc
        P.probability i * P.probability j ≤ ∑ v' : Fin n,
            if G.Adj u v' ∧ u ∈ P.vertices i ∧ v' ∈ P.vertices j then
              P.probability i * P.probability j else 0 := by
          have hs := Finset.single_le_sum (fun v' _ => hn u v') (Finset.mem_univ v)
          simpa only [if_pos (And.intro huv (And.intro hui hvj))] using hs
        _ ≤ _ := Finset.single_le_sum (fun u' _ => Finset.sum_nonneg fun v' _ => hn u' v')
          (Finset.mem_univ u)
    · exact Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => hn u v
  have hswap : (∑ i, ∑ j, ∑ u : Fin n, ∑ v : Fin n,
      if G.Adj u v ∧ u ∈ P.vertices i ∧ v ∈ P.vertices j then
        P.probability i * P.probability j else 0) =
      ∑ u : Fin n, ∑ v : Fin n, ∑ i, ∑ j,
        if G.Adj u v ∧ u ∈ P.vertices i ∧ v ∈ P.vertices j then
          P.probability i * P.probability j else 0 := by
    rw [swap_inner_sums]
    apply Finset.sum_congr rfl
    intro u _
    exact swap_inner_sums _
  calc
    adjacencyProbability G P ≤ ∑ i, ∑ j, ∑ u : Fin n, ∑ v : Fin n,
        if G.Adj u v ∧ u ∈ P.vertices i ∧ v ∈ P.vertices j then
          P.probability i * P.probability j else 0 :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair i j
    _ = ∑ u : Fin n, ∑ v : Fin n, ∑ i, ∑ j,
        if G.Adj u v ∧ u ∈ P.vertices i ∧ v ∈ P.vertices j then
          P.probability i * P.probability j else 0 := hswap
    _ = adjacencyMass G (load P) := by
      unfold adjacencyMass
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro v _
      by_cases huv : G.Adj u v
      · simp only [huv, true_and, if_true]
        exact pair_load_product P u v
      · simp [huv]

theorem adjacencyMass_scale {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℝ) (c : ℝ) :
    adjacencyMass G (fun v => c * x v) = c ^ 2 * adjacencyMass G x := by
  unfold adjacencyMass
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> ring

/--
---
conclusion: Lax263307.PathSampling.sampling_bounds
---
Substitute the vertex-load bound into the two union bounds. The estimate
`x_v² ≤ x_v` and total cost at most `k` control intersections; the edge-cost hypothesis
controls adjacency. Summing the same load bound controls expected size.
-/
theorem sampling_bounds {n q : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (P : Distribution n q) (x : Fin n → ℝ) (k ℓ p : ℝ)
    (k_positive : 0 < k) (ℓ_nonnegative : 0 ≤ ℓ) (p_positive : 0 < p)
    (cost_bounds : ∀ v, 0 ≤ x v ∧ x v ≤ 1) (mass : (∑ v, x v) ≤ k)
    (load_bound : ∀ v, load P v ≤ ℓ * x v / k)
    (edge_bound : edgeCost G x ≤ k ^ 2 / p) :
    collisionProbability P ≤ ℓ ^ 2 / k ∧
      adjacencyProbability G P ≤ 2 * ℓ ^ 2 / p ∧ expectedSize P ≤ ℓ := by
  let c := ℓ / k
  have hc : 0 ≤ c := div_nonneg ℓ_nonnegative k_positive.le
  have hload (v : Fin n) : load P v ≤ c * x v := by
    simpa only [c, div_eq_mul_inv, mul_right_comm] using load_bound v
  have hsq (v : Fin n) : (load P v) ^ 2 ≤ c ^ 2 * x v := by
    have hscale : 0 ≤ c * x v := mul_nonneg hc (cost_bounds v).1
    have hpow : (load P v) ^ 2 ≤ (c * x v) ^ 2 :=
      (sq_le_sq₀ (load_nonnegative P v) hscale).mpr (hload v)
    have hx : (x v) ^ 2 ≤ x v := by nlinarith [(cost_bounds v).1, (cost_bounds v).2]
    calc
      (load P v) ^ 2 ≤ (c * x v) ^ 2 := hpow
      _ = c ^ 2 * (x v) ^ 2 := by ring
      _ ≤ c ^ 2 * x v := mul_le_mul_of_nonneg_left hx (sq_nonneg c)
  have hcoll : collisionProbability P ≤ ℓ ^ 2 / k := by
    calc
      collisionProbability P ≤ ∑ v, (load P v) ^ 2 :=
        Lax263307.PathSampling.collision_union_bound P
      _ ≤ ∑ v, c ^ 2 * x v := Finset.sum_le_sum fun v _ => hsq v
      _ = c ^ 2 * (∑ v, x v) := by rw [← Finset.mul_sum]
      _ ≤ c ^ 2 * k := mul_le_mul_of_nonneg_left mass (sq_nonneg c)
      _ = ℓ ^ 2 / k := by dsimp [c]; field_simp
  have hadj : adjacencyMass G (load P) ≤ c ^ 2 * adjacencyMass G x := by
    rw [← adjacencyMass_scale G x c]
    unfold adjacencyMass
    apply Finset.sum_le_sum
    intro u _
    apply Finset.sum_le_sum
    intro v _
    split_ifs
    · exact mul_le_mul (hload u) (hload v) (load_nonnegative P v)
        (mul_nonneg hc (cost_bounds u).1)
    · exact le_rfl
  have he : adjacencyMass G x ≤ 2 * k ^ 2 / p := by
    unfold edgeCost at edge_bound
    calc
      adjacencyMass G x ≤ 2 * (k ^ 2 / p) := by linarith
      _ = 2 * k ^ 2 / p := by ring
  have hadj' : adjacencyProbability G P ≤ 2 * ℓ ^ 2 / p := by
    calc
      adjacencyProbability G P ≤ adjacencyMass G (load P) :=
        Lax263307.PathSampling.adjacency_union_bound G P
      _ ≤ c ^ 2 * adjacencyMass G x := hadj
      _ ≤ c ^ 2 * (2 * k ^ 2 / p) := mul_le_mul_of_nonneg_left he (sq_nonneg c)
      _ = 2 * ℓ ^ 2 / p := by dsimp [c]; field_simp
  have hsize : expectedSize P ≤ ℓ := by
    rw [Lax263307.PathSampling.expected_size_identity]
    calc
      (∑ v, load P v) ≤ ∑ v, c * x v := Finset.sum_le_sum fun v _ => hload v
      _ = c * (∑ v, x v) := by rw [← Finset.mul_sum]
      _ ≤ c * k := mul_le_mul_of_nonneg_left mass hc
      _ = ℓ := by dsimp [c]; field_simp
  exact ⟨hcoll, hadj', hsize⟩

end Lax263307Proofs.PathSampling
