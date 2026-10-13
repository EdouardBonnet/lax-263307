import Lax263307.VertexSplitting
import Mathlib.Algebra.BigOperators.Fin

namespace Lax263307Proofs.VertexSplitting

open scoped NNReal NNRat
open Lax263307.VertexSplitting Lax455465.RationalEncoding Lax455465.ProductNetwork
open Lax455465.ConcurrentFlow

@[simp] theorem original_minus {n : ℕ} (v : Fin n) : original (minus v) = v := by
  apply Fin.ext
  simp [original, minus]

@[simp] theorem original_plus {n : ℕ} (v : Fin n) : original (plus v) = v := by
  apply Fin.ext
  dsimp [original, plus]
  omega

theorem capacity_reverse {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (large : ℚ≥0) (v : Fin n) :
    (splitInstance G x large).capacity (plus v) (minus v) = large := by
  simp [splitInstance, minus, plus, original]

theorem capacity_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (large : ℚ≥0) (u v : Fin n) (huv : G.Adj u v) :
    (splitInstance G x large).capacity (plus u) (minus v) = large := by
  simp only [splitInstance, original_plus, original_minus]
  simp [minus, plus, huv]

theorem port_cases {n : ℕ} (v : Fin (2 * n)) :
    v = minus (original v) ∨ v = plus (original v) := by
  by_cases heven : v.val % 2 = 0
  · left
    apply Fin.ext
    dsimp [minus, original]
    omega
  · right
    apply Fin.ext
    dsimp [plus, original]
    omega

theorem capacity_le_cut {N : ℕ} (I : Network N) (U : Finset (Fin N))
    (a b : Fin N) (ha : a ∈ U) (hb : b ∉ U) :
    I.capacity a b ≤ cutCapacity I U := by
  classical
  exact (Finset.single_le_sum (f := I.capacity a) (fun _ _ => zero_le) (Finset.mem_compl.mpr hb)).trans
    (Finset.single_le_sum (f := fun u => ∑ v ∈ Uᶜ, I.capacity u v) (fun _ _ => zero_le) ha)

theorem small_cut_reverse_closed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (large : ℚ≥0) (U : Finset (Fin (2 * n)))
    (small : cutCapacity (splitInstance G x large).network U < (large : ℝ≥0))
    (v : Fin n) (hv : plus v ∈ U) : minus v ∈ U := by
  by_contra hn
  have h := capacity_le_cut (splitInstance G x large).network U (plus v) (minus v) hv hn
  change ((splitInstance G x large).capacity (plus v) (minus v) : ℝ≥0) ≤ _ at h
  rw [capacity_reverse] at h
  exact (not_lt_of_ge h) small

theorem small_cut_no_cross_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (large : ℚ≥0) (U : Finset (Fin (2 * n)))
    (small : cutCapacity (splitInstance G x large).network U < (large : ℝ≥0))
    (u v : Fin n) (hu : plus u ∈ U) (hv : minus v ∉ U) : ¬G.Adj u v := by
  intro huv
  have h := capacity_le_cut (splitInstance G x large).network U (plus u) (minus v) hu hv
  change ((splitInstance G x large).capacity (plus u) (minus v) : ℝ≥0) ≤ _ at h
  rw [capacity_edge G x large u v huv] at h
  exact (not_lt_of_ge h) small

theorem original_in_left {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (large : ℚ≥0) (U : Finset (Fin (2 * n)))
    (small : cutCapacity (splitInstance G x large).network U < (large : ℝ≥0))
    (v : Fin (2 * n)) (hv : v ∈ U) : original v ∈ leftShore U := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rcases port_cases v with he | he
  · exact he ▸ hv
  · exact small_cut_reverse_closed G x large U small _ (he ▸ hv)

theorem original_in_right {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (large : ℚ≥0) (U : Finset (Fin (2 * n)))
    (small : cutCapacity (splitInstance G x large).network U < (large : ℝ≥0))
    (v : Fin (2 * n)) (hv : v ∉ U) : original v ∈ rightShore U := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rcases port_cases v with he | he
  · intro hp
    exact hv (he.symm ▸ small_cut_reverse_closed G x large U small _ hp)
  · intro hp
    exact hv (he.symm ▸ hp)

def encodePort {n : ℕ} (v : Fin (2 * n)) : Fin n × Fin 2 :=
  (original v, ⟨v.val % 2, by omega⟩)

theorem encodePort_injective (n : ℕ) : Function.Injective (encodePort (n := n)) := by
  intro v w he
  have hfirst := congrArg (fun a => a.1.val) he
  have hsecond := congrArg (fun a => a.2.val) he
  apply Fin.ext
  dsimp [encodePort, original] at hfirst hsecond
  omega

theorem shore_card_bounds {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (large : ℚ≥0) (U : Finset (Fin (2 * n)))
    (small : cutCapacity (splitInstance G x large).network U < (large : ℝ≥0)) :
    U.card ≤ 2 * (leftShore U).card ∧ Uᶜ.card ≤ 2 * (rightShore U).card := by
  have hleft : U.image encodePort ⊆ (leftShore U).product Finset.univ := by
    intro a ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_product.mpr ⟨original_in_left G x large U small v hv, Finset.mem_univ _⟩
  have hright : Uᶜ.image encodePort ⊆ (rightShore U).product Finset.univ := by
    intro a ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_product.mpr ⟨original_in_right G x large U small v
      (Finset.mem_compl.mp hv), Finset.mem_univ _⟩
  have hcardL := Finset.card_le_card hleft
  have hcardR := Finset.card_le_card hright
  rw [Finset.card_image_of_injective _ (encodePort_injective n)] at hcardL hcardR
  simpa [Nat.mul_comm] using And.intro hcardL hcardR

/--
---
conclusion: Lax263307.VertexSplitting.small_cut_separation
---
No large-capacity arc crosses a cut smaller than that capacity. Reverse arcs
force every inside plus port's minus port inside; graph arcs forbid an edge
between the two exclusive shores. Encode each split vertex by its original
vertex and port to bound shore sizes by twice the corresponding original
shore sizes.

# Attribution

Bonnet–Chang, cut projection in Lemma 7.
-/
theorem small_cut_separation {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (large : ℚ≥0) (U : Finset (Fin (2 * n)))
    (small : cutCapacity (splitInstance G x large).network U < (large : ℝ≥0))
    (nonempty : U.Nonempty) (proper : Uᶜ.Nonempty) :
    (leftShore U).Nonempty ∧ (rightShore U).Nonempty ∧
      leftShore U ∪ rightShore U = Finset.univ ∧
      (∀ u ∈ leftShore U \ rightShore U, ∀ v ∈ rightShore U \ leftShore U, ¬G.Adj u v) ∧
      U.card ≤ 2 * (leftShore U).card ∧ Uᶜ.card ≤ 2 * (rightShore U).card := by
  have hleft : (leftShore U).Nonempty := by
    obtain ⟨v, hv⟩ := nonempty
    exact ⟨original v, original_in_left G x large U small v hv⟩
  have hright : (rightShore U).Nonempty := by
    obtain ⟨v, hv⟩ := proper
    exact ⟨original v, original_in_right G x large U small v (Finset.mem_compl.mp hv)⟩
  have hcover : leftShore U ∪ rightShore U = Finset.univ := by
    ext v
    simp only [leftShore, rightShore, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hv : minus v ∈ U
    · exact iff_true_intro (Or.inl hv)
    · exact iff_true_intro (Or.inr fun hp => hv (small_cut_reverse_closed G x large U small v hp))
  have hsep : ∀ u ∈ leftShore U \ rightShore U,
      ∀ v ∈ rightShore U \ leftShore U, ¬G.Adj u v := by
    intro u hu v hv
    have hu' : plus u ∈ U := by
      have := (Finset.mem_sdiff.mp hu).2
      simpa [rightShore] using this
    have hv' : minus v ∉ U := by
      have := (Finset.mem_sdiff.mp hv).2
      simpa [leftShore] using this
    exact small_cut_no_cross_edge G x large U small u v hu' hv'
  exact ⟨hleft, hright, hcover, hsep, shore_card_bounds G x large U small⟩

/--
---
conclusion: Lax263307.VertexSplitting.split_certificate
---
Instantiate the registered directed uniform algorithm on the split network.
Its vertex weights are all one, and its order is twice the original order.
The same total solver function and actual RAM guarantee apply to every
rational split instance.

# Attribution

Lax455465 directed uniform flow–cut theorem; the split construction is from
Bonnet–Chang, Lemma 7.
-/
theorem split_certificate :
  ∃ (solve : List ℕ → List ℕ) (C : ℝ), Lax759944.RamPolytime.RamPolytime solve ∧ 0 < C ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (x : Fin n → ℚ≥0) (large : ℚ≥0), 0 < n →
      let I := splitInstance G x large
      ∃ certificate : Lax455465.FlowCutCertificate.Certificate (2 * n),
        solve (encodeInput .directed I) = Lax455465.FlowCutCertificate.encodeCertificate certificate ∧
        AdmissibleCut I.weights certificate.cut ∧
        IsArcConcurrentFlow .directed I.network I.weights
          (certificate.flow.value : ℝ≥0) certificate.flow.flow ∧
        (ratioCost I.network I.weights certificate.cut : ℝ) ≤
          C * logFactor (2 * n) * (certificate.flow.value : ℝ) := by
  obtain ⟨solve, C, hp, hC, hsolve⟩ :=
    Lax455465.RamDirectedUniformFlowCut.exists_polynomial_time_flow_cut
  refine ⟨solve, C, hp, hC, ?_⟩
  intro n G inst x large hn
  exact hsolve (2 * n) (splitInstance G x large) (fun _ => rfl) (by omega)

theorem sum_ports {n : ℕ} (f : Fin (2 * n) → ℝ≥0) :
    (∑ s, f s) = ∑ v, (f (minus v) + f (plus v)) := by
  classical
  have hsurj : Function.Surjective (encodePort (n := n)) := by
    rintro ⟨v, p⟩
    fin_cases p
    · exact ⟨minus v, by
        apply Prod.ext
        · exact original_minus v
        · apply Fin.ext; simp [encodePort, minus]⟩
    · exact ⟨plus v, by
        apply Prod.ext
        · exact original_plus v
        · apply Fin.ext; simp [encodePort, plus]⟩
  let e := Equiv.ofBijective encodePort ⟨encodePort_injective n, hsurj⟩
  have heq : (∑ s, f s) = ∑ a : Fin n × Fin 2,
      if a.2 = 0 then f (minus a.1) else f (plus a.1) := by
    apply Fintype.sum_equiv e
    intro s
    change f s = if (encodePort s).2 = 0 then f (minus (original s)) else f (plus (original s))
    by_cases hp : s.val % 2 = 0
    · have hp' : (encodePort s).2 = 0 := Fin.ext hp
      rw [if_pos hp']
      congr 1
      apply Fin.ext
      dsimp [minus, original]
      omega
    · have hp' : (encodePort s).2 ≠ 0 := by
        intro h
        exact hp (congrArg Fin.val h)
      rw [if_neg hp']
      congr 1
      apply Fin.ext
      dsimp [plus, original]
      omega
  rw [heq, Fintype.sum_prod_type]
  simp [Fin.sum_univ_two]

theorem capacity_minus {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (large : ℚ≥0) (v : Fin n) (t : Fin (2 * n)) :
    (splitInstance G x large).capacity (minus v) t = if t = plus v then x v else 0 := by
  simp only [splitInstance]
  rw [original_minus]
  simp only [minus, Nat.mul_mod_right, zero_ne_one,
    false_and, if_false, true_and]
  have heq : t.val = 2 * v.val + 1 ↔ t = plus v := by
    exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  simp only [heq]

theorem capacity_plus_plus {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (large : ℚ≥0) (u v : Fin n) :
    (splitInstance G x large).capacity (plus u) (plus v) = 0 := by
  have hbad : ¬(2 * v.val + 1 = 2 * u.val) := by omega
  simp [splitInstance, plus, hbad]

theorem capacity_plus_minus {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (large : ℚ≥0) (u v : Fin n) :
    (splitInstance G x large).capacity (plus u) (minus v) =
      if u = v ∨ G.Adj u v then large else 0 := by
  have hback : v.val = u.val ↔ u = v := by
    exact ⟨fun h => Fin.ext h.symm, fun h => congrArg Fin.val h.symm⟩
  simp only [splitInstance, original_plus, original_minus]
  simp [plus, minus, hback, ite_or]

theorem small_cut_plus_zero {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (large : ℚ≥0) (U : Finset (Fin (2 * n)))
    (small : cutCapacity (splitInstance G x large).network U < (large : ℝ≥0))
    (u : Fin n) (hu : plus u ∈ U) (t : Fin (2 * n)) (ht : t ∉ U) :
    (splitInstance G x large).capacity (plus u) t = 0 := by
  rcases port_cases t with h | h
  · rw [h, capacity_plus_minus]
    have hv : minus (original t) ∉ U := by intro hv; exact ht (h.symm ▸ hv)
    have hne : u ≠ original t := by
      intro he
      exact hv (he ▸ small_cut_reverse_closed G x large U small u hu)
    have hadj := small_cut_no_cross_edge G x large U small u (original t) hu hv
    simp [hne, hadj]
  · rw [h, capacity_plus_plus]

/--
---
conclusion: Lax263307.VertexSplitting.small_cut_cost
---
Sum the cut contributions separately for input and output ports. Every output
port contributes zero, since no large-capacity arc leaves the cut. An input
port contributes exactly its vertex cost when it lies inside and its paired
output port lies outside. These are precisely the separator's vertices.

# Attribution

Bonnet–Chang, capacity identity in the vertex-splitting reduction of Lemma 7.
-/
theorem small_cut_cost {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (large : ℚ≥0) (U : Finset (Fin (2 * n)))
    (small : cutCapacity (splitInstance G x large).network U < (large : ℝ≥0)) :
    cutCapacity (splitInstance G x large).network U =
      ∑ v ∈ leftShore U ∩ rightShore U, (x v : ℝ≥0) := by
  classical
  let I := splitInstance G x large
  let f (s : Fin (2 * n)) : ℝ≥0 := if s ∈ U then ∑ t ∈ Uᶜ, I.network.capacity s t else 0
  have hminus (v : Fin n) : f (minus v) =
      if minus v ∈ U ∧ plus v ∉ U then (x v : ℝ≥0) else 0 := by
    have hinner : (∑ t ∈ Uᶜ, I.network.capacity (minus v) t) =
        if plus v ∉ U then (x v : ℝ≥0) else 0 := by
      change (∑ t ∈ Uᶜ, ((splitInstance G x large).capacity (minus v) t : ℝ≥0)) = _
      simp_rw [capacity_minus]
      by_cases hp : plus v ∈ U
      · rw [if_neg (not_not.mpr hp)]
        apply Finset.sum_eq_zero
        intro t ht
        have hne : t ≠ plus v := fun he => (Finset.mem_compl.mp ht) (he.symm ▸ hp)
        simp [hne]
      · rw [if_pos hp, Finset.sum_eq_single (plus v)]
        · simp
        · intro t ht hne
          simp [hne]
        · simp [hp]
    dsimp [f]
    rw [hinner]
    by_cases hm : minus v ∈ U <;> by_cases hp : plus v ∈ U <;> simp [hm, hp]
  have hplus (v : Fin n) : f (plus v) = 0 := by
    dsimp [f]
    split_ifs with hv
    · apply Finset.sum_eq_zero
      intro t ht
      change ((splitInstance G x large).capacity (plus v) t : ℝ≥0) = 0
      rw [small_cut_plus_zero G x large U small v hv t (Finset.mem_compl.mp ht)]
      simp
    · rfl
  have hcapacity : cutCapacity I.network U = ∑ s, f s := by
    simp only [f, Finset.sum_ite_mem, Finset.univ_inter]
    rfl
  rw [hcapacity, sum_ports]
  simp_rw [hminus, hplus, add_zero]
  have hshore : ∀ v : Fin n, (minus v ∈ U ∧ plus v ∉ U) ↔ v ∈ leftShore U ∩ rightShore U := by
    intro v
    simp [leftShore, rightShore]
  simp_rw [hshore]
  simpa only [Finset.univ_inter] using
    (Finset.sum_ite_mem (Finset.univ : Finset (Fin n)) (leftShore U ∩ rightShore U)
      (fun v => (x v : ℝ≥0)))

/--
---
conclusion: Lax263307.VertexSplitting.separator_cost_bound
---
Uniform weights make the cut demand the product of its shore cardinalities.
Clear this positive denominator, substitute the cut-capacity identity, and
bound each split shore by twice its projected shore. The two factors of two
give the separator bound.

# Attribution

Bonnet–Chang, cut ratio estimate in Lemma 7.
-/
theorem separator_cost_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (large : ℚ≥0) (U : Finset (Fin (2 * n))) (ρ : ℝ)
    (nonnegative : 0 ≤ ρ)
    (small : cutCapacity (splitInstance G x large).network U < (large : ℝ≥0))
    (admissible : AdmissibleCut (splitInstance G x large).weights U)
    (ratio : (ratioCost (splitInstance G x large).network
      (splitInstance G x large).weights U : ℝ) ≤ ρ) :
    (∑ v ∈ leftShore U ∩ rightShore U, (x v : ℝ)) ≤
      4 * ρ * (leftShore U).card * (rightShore U).card := by
  classical
  let I := splitInstance G x large
  have hweights : I.weights = uniformWeight (2 * n) := by
    funext v
    simp [I, splitInstance, RationalInstance.weights, uniformWeight]
  have hmass (V : Finset (Fin (2 * n))) : mass I.weights V = (V.card : ℝ≥0) := by
    simp [hweights, mass, uniformWeight]
  have hleft : (0 : ℝ) < U.card := by
    have h := admissible.1
    rw [hmass] at h
    exact_mod_cast h
  have hright : (0 : ℝ) < Uᶜ.card := by
    have h := admissible.2
    rw [hmass] at h
    exact_mod_cast h
  have hratio : (cutCapacity I.network U : ℝ) / ((U.card : ℝ) * Uᶜ.card) ≤ ρ := by
    change (ratioCost I.network I.weights U : ℝ) ≤ ρ at ratio
    simpa only [ratioCost, hmass, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast] using ratio
  have hcap := (div_le_iff₀ (mul_pos hleft hright)).mp hratio
  have hcards := shore_card_bounds G x large U small
  have hL : (U.card : ℝ) ≤ 2 * (leftShore U).card := by exact_mod_cast hcards.1
  have hR : (Uᶜ.card : ℝ) ≤ 2 * (rightShore U).card := by exact_mod_cast hcards.2
  have hprod := mul_le_mul hL hR (by positivity) (by positivity)
  have hρ := mul_le_mul_of_nonneg_left hprod nonnegative
  have hcost : (cutCapacity I.network U : ℝ) =
      ∑ v ∈ leftShore U ∩ rightShore U, (x v : ℝ) := by
    rw [Lax263307.VertexSplitting.small_cut_cost G x large U small]
    push_cast
    apply Finset.sum_congr rfl
    intro v _
    norm_cast
  rw [hcost] at hcap
  nlinarith

theorem small_cut_of_low_flow {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (large : ℚ≥0)
    (certificate : Lax455465.FlowCutCertificate.Certificate (2 * n)) (ρ γ : ℝ)
    (nonnegative : 0 ≤ ρ) (positive : 0 < γ)
    (admissible : AdmissibleCut (splitInstance G x large).weights certificate.cut)
    (ratio : (ratioCost (splitInstance G x large).network
      (splitInstance G x large).weights certificate.cut : ℝ) ≤
        ρ * (certificate.flow.value : ℝ))
    (low_value : (certificate.flow.value : ℝ) < 1 / γ)
    (large_capacity : ρ * (2 * n : ℕ) ^ 2 / γ < (large : ℝ)) :
    cutCapacity (splitInstance G x large).network certificate.cut < (large : ℝ≥0) := by
  classical
  let I := splitInstance G x large
  let U := certificate.cut
  have hweights : I.weights = uniformWeight (2 * n) := by
    funext v
    simp [I, splitInstance, RationalInstance.weights, uniformWeight]
  have hmass (V : Finset (Fin (2 * n))) : mass I.weights V = (V.card : ℝ≥0) := by
    simp [hweights, mass, uniformWeight]
  have hleft : (0 : ℝ) < U.card := by
    have h := admissible.1
    change 0 < mass I.weights U at h
    rw [hmass] at h
    exact_mod_cast h
  have hright : (0 : ℝ) < Uᶜ.card := by
    have h := admissible.2
    change 0 < mass I.weights Uᶜ at h
    rw [hmass] at h
    exact_mod_cast h
  have hratio : (cutCapacity I.network U : ℝ) / ((U.card : ℝ) * Uᶜ.card) ≤
      ρ * (certificate.flow.value : ℝ) := by
    change (ratioCost I.network I.weights U : ℝ) ≤ _ at ratio
    simpa only [ratioCost, hmass, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast] using ratio
  have hcap := (div_le_iff₀ (mul_pos hleft hright)).mp hratio
  have hL : (U.card : ℝ) ≤ (2 * n : ℕ) := by
    exact_mod_cast (show U.card ≤ 2 * n by simpa using Finset.card_le_univ U)
  have hR : (Uᶜ.card : ℝ) ≤ (2 * n : ℕ) := by
    exact_mod_cast (show Uᶜ.card ≤ 2 * n by simpa using Finset.card_le_univ Uᶜ)
  have hproduct : (U.card : ℝ) * Uᶜ.card ≤ ((2 * n : ℕ) : ℝ) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hL hR hright.le (by positivity)
  have hflow := mul_le_mul_of_nonneg_left low_value.le nonnegative
  have hscale : 0 ≤ ρ * (1 / γ) := mul_nonneg nonnegative (by positivity)
  have hbound : (cutCapacity I.network U : ℝ) ≤ ρ * (2 * n : ℕ) ^ 2 / γ := by
    calc
      (cutCapacity I.network U : ℝ) ≤ (ρ * (certificate.flow.value : ℝ)) *
          ((U.card : ℝ) * Uᶜ.card) := hcap
      _ ≤ (ρ * (1 / γ)) * ((U.card : ℝ) * Uᶜ.card) :=
        mul_le_mul_of_nonneg_right hflow (mul_nonneg hleft.le hright.le)
      _ ≤ (ρ * (1 / γ)) * ((2 * n : ℕ) : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hproduct hscale
      _ = ρ * (2 * n : ℕ) ^ 2 / γ := by ring
  have hlt := hbound.trans_lt large_capacity
  change (cutCapacity I.network U : ℝ≥0) < (large : ℝ≥0)
  exact_mod_cast hlt

/--
---
conclusion: Lax263307.VertexSplitting.flow_or_separation
---
Compare the certificate's flow value with `1/γ`. A smaller value bounds the
cut capacity by `rho(2n)²/γ`, below the chosen large capacity. The cut therefore
projects to a nontrivial separation. Its ratio is at most `rho/γ`, and the
shore and capacity identities give the desired original separator cost.
The other branch retains the certificate's feasible high-value split flow.

# Attribution

Bonnet–Chang, the two alternatives in the vertex-splitting reduction of Lemma 7.
-/
theorem flow_or_separation {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (large : ℚ≥0)
    (certificate : Lax455465.FlowCutCertificate.Certificate (2 * n)) (ρ γ : ℝ)
    (nonnegative : 0 ≤ ρ) (positive : 0 < γ)
    (admissible : AdmissibleCut (splitInstance G x large).weights certificate.cut)
    (flow_valid : IsArcConcurrentFlow .directed (splitInstance G x large).network
      (splitInstance G x large).weights (certificate.flow.value : ℝ≥0) certificate.flow.flow)
    (ratio : (ratioCost (splitInstance G x large).network
      (splitInstance G x large).weights certificate.cut : ℝ) ≤
        ρ * (certificate.flow.value : ℝ))
    (large_capacity : ρ * (2 * n : ℕ) ^ 2 / γ < (large : ℝ)) :
    ((1 / γ ≤ (certificate.flow.value : ℝ)) ∧
      IsArcConcurrentFlow .directed (splitInstance G x large).network
        (splitInstance G x large).weights (certificate.flow.value : ℝ≥0) certificate.flow.flow) ∨
    ((leftShore certificate.cut).Nonempty ∧ (rightShore certificate.cut).Nonempty ∧
      leftShore certificate.cut ∪ rightShore certificate.cut = Finset.univ ∧
      (∀ u ∈ leftShore certificate.cut \ rightShore certificate.cut,
        ∀ v ∈ rightShore certificate.cut \ leftShore certificate.cut, ¬G.Adj u v) ∧
      (∑ v ∈ leftShore certificate.cut ∩ rightShore certificate.cut, (x v : ℝ)) ≤
        4 * ρ * (leftShore certificate.cut).card * (rightShore certificate.cut).card / γ) := by
  by_cases hhigh : 1 / γ ≤ (certificate.flow.value : ℝ)
  · exact Or.inl ⟨hhigh, flow_valid⟩
  · have hlow : (certificate.flow.value : ℝ) < 1 / γ := lt_of_not_ge hhigh
    have hsmall := small_cut_of_low_flow G x large certificate ρ γ nonnegative positive
      admissible ratio hlow large_capacity
    have hnonempty : certificate.cut.Nonempty := by
      by_contra he
      have hzero := Finset.not_nonempty_iff_eq_empty.mp he
      have h := admissible.1
      simp [hzero, mass] at h
    have hproper : certificate.cutᶜ.Nonempty := by
      by_contra he
      have hzero := Finset.not_nonempty_iff_eq_empty.mp he
      have h := admissible.2
      simp [hzero, mass] at h
    obtain ⟨hA, hB, hcover, hsep, _, _⟩ :=
      Lax263307.VertexSplitting.small_cut_separation G x large certificate.cut hsmall hnonempty hproper
    have hratio : (ratioCost (splitInstance G x large).network
      (splitInstance G x large).weights certificate.cut : ℝ) ≤ ρ / γ := by
      calc
        _ ≤ ρ * (certificate.flow.value : ℝ) := ratio
        _ ≤ ρ * (1 / γ) := mul_le_mul_of_nonneg_left hlow.le nonnegative
        _ = ρ / γ := by ring
    have hcost := Lax263307.VertexSplitting.separator_cost_bound G x large certificate.cut
      (ρ / γ) (div_nonneg nonnegative positive.le) hsmall admissible hratio
    right
    refine ⟨hA, hB, hcover, hsep, ?_⟩
    calc
      _ ≤ 4 * (ρ / γ) * (leftShore certificate.cut).card * (rightShore certificate.cut).card := hcost
      _ = 4 * ρ * (leftShore certificate.cut).card * (rightShore certificate.cut).card / γ := by ring

end Lax263307Proofs.VertexSplitting
