import Lax263307.LightSeparators
import Lax263307.ForcedSeparation
import Lax263307.CutTraces
import Mathlib.Tactic

namespace Lax263307Proofs.LightSeparators

open scoped NNReal NNRat
open Lax263307.GraphClasses Lax263307.EdgeSublinearSeparators
open Lax263307.PowerBagBounds Lax263307.VertexSplitting
open Lax263307.RepeatedCutAccounting Lax263307.Entropy
open Lax455465.ProductNetwork Lax455465.ConcurrentFlow Lax455465.RationalEncoding

theorem logFactor_nonnegative (n : ℕ) : 0 ≤ logFactor n := by
  unfold logFactor
  apply div_nonneg _ (Real.log_pos (by norm_num)).le
  by_cases hn : n = 0
  · simp [hn]
  · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))

theorem logFactor_upper (n : ℕ) : logFactor n ≤ (Nat.log2 n : ℝ) + 1 := by
  by_cases hn : n = 0
  · simp [hn, logFactor]
  · have hp := (Nat.lt_pow_succ_log_self Nat.one_lt_two n).le
    rw [← Nat.log2_eq_log_two] at hp
    have hpr : (n : ℝ) ≤ (2 : ℝ) ^ (Nat.log2 n + 1) := by exact_mod_cast hp
    have h := Real.log_le_log (by exact_mod_cast (show 0 < n by omega)) hpr
    rw [Real.log_pow, Nat.cast_add, Nat.cast_one] at h
    exact (div_le_iff₀ (Real.log_pos (by norm_num))).mpr h

theorem logFactor_mono {m n : ℕ} (positive : 0 < m) (bound : m ≤ n) : logFactor m ≤ logFactor n :=
  div_le_div_of_nonneg_right (Real.log_le_log (by exact_mod_cast positive) (by exact_mod_cast bound))
    (Real.log_pos (by norm_num)).le

theorem bounded_ratio (C : ℝ) (positive : 0 < C) :
    ∃ B : ℕ, 0 < B ∧ ∀ n r : ℕ, 0 < r → r ≤ n →
      C * logFactor (2 * r) ≤ (B : ℝ) * ((Nat.log2 (2 * n) : ℝ) + 1) := by
  let B := Nat.ceil C
  have hB : 0 < B := Nat.ceil_pos.mpr positive
  refine ⟨B, hB, ?_⟩
  intro n r hr hrn
  have hlog := (logFactor_mono (by omega : 0 < 2 * r) (Nat.mul_le_mul_left 2 hrn)).trans
    (logFactor_upper (2 * n))
  exact mul_le_mul (Nat.le_ceil C) hlog (logFactor_nonnegative _) (Nat.cast_nonneg B)


theorem sum_embedding {m n : ℕ} (f : Fin m ↪ Fin n) (x : Fin n → ℝ)
    (nonnegative : ∀ v, 0 ≤ x v) : (∑ v, x (f v)) ≤ ∑ v, x v := by
  classical
  calc
    _ = ∑ v ∈ Finset.univ.image f, x v := (Finset.sum_image (fun _ _ _ _ h => f.injective h)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v _ _ => nonnegative v)

theorem edge_cost_embedding {m n : ℕ} (H : SimpleGraph (Fin m)) (G : SimpleGraph (Fin n))
    [DecidableRel H.Adj] [DecidableRel G.Adj] (f : H ↪g G)
    (x : Fin n → ℝ) (nonnegative : ∀ v, 0 ≤ x v) :
    edgeCost H (x ∘ f) ≤ edgeCost G x := by
  classical
  unfold edgeCost adjacencyMass
  apply div_le_div_of_nonneg_right _ (by norm_num)
  have hnonneg (u v : Fin n) : 0 ≤ (if G.Adj u v then x u * x v else 0) := by
    split_ifs
    · exact mul_nonneg (nonnegative u) (nonnegative v)
    · exact le_refl _
  calc
    (∑ u : Fin m, ∑ v : Fin m, if H.Adj u v then (x ∘ f) u * (x ∘ f) v else 0) =
        ∑ u : Fin m, ∑ v : Fin m, if G.Adj (f u) (f v) then x (f u) * x (f v) else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro v _
      simp only [Function.comp_apply, f.map_adj_iff]
    _ ≤ ∑ u : Fin m, ∑ v : Fin n, if G.Adj (f u) v then x (f u) * x v else 0 :=
      Finset.sum_le_sum (fun u _ => sum_embedding f.toEmbedding _ (hnonneg (f u)))
    _ ≤ _ := sum_embedding f.toEmbedding _ (fun u => Finset.sum_nonneg (fun v _ => hnonneg u v))


theorem small_piece {n : ℕ} (A B : Finset (Fin n)) (cover : A ∪ B = Finset.univ)
    (smaller : B.card ≤ A.card) : 2 * (B \ A).card ≤ n := by
  have h := Finset.card_union_add_card_inter A B
  rw [cover, Finset.card_univ, Fintype.card_fin] at h
  have hpart := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm B A] at hpart
  omega

theorem orient {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → ℝ) (ρ γ : ℝ)
    (A B : Finset (Fin n)) (left_nonempty : A.Nonempty) (right_nonempty : B.Nonempty)
    (cover : A ∪ B = Finset.univ)
    (separated : ∀ u ∈ A \ B, ∀ v ∈ B \ A, ¬G.Adj u v)
    (bound : cost x (A ∩ B) ≤ 4 * ρ * A.card * B.card / γ) :
    ∃ A' B' : Finset (Fin n), A' ∪ B' = Finset.univ ∧ B'.Nonempty ∧
      2 * (B' \ A').card ≤ n ∧
      (∀ u ∈ A' \ B', ∀ v ∈ B' \ A', ¬G.Adj u v) ∧
      cost x (A' ∩ B') ≤ 4 * ρ * A'.card * B'.card / γ := by
  by_cases h : B.card ≤ A.card
  · exact ⟨A, B, cover, right_nonempty, small_piece A B cover h, separated, bound⟩
  · refine ⟨B, A, by rw [Finset.union_comm]; exact cover, left_nonempty,
      small_piece B A (by rw [Finset.union_comm]; exact cover) (by omega), ?_, ?_⟩
    · intro u hu v hv hadj
      exact separated v hv u hu hadj.symm
    · rw [Finset.inter_comm]
      convert bound using 1; ring


theorem project_cut {r n : ℕ} (H : SimpleGraph (Fin r)) (G : SimpleGraph (Fin n))
    (f : H ↪g G) (R : Finset (Fin n)) (onto : Finset.univ.image f = R)
    (x : Fin n → ℝ) (ρ γ : ℝ) (A B : Finset (Fin r))
    (cover : A ∪ B = Finset.univ) (nonempty : B.Nonempty)
    (small : 2 * (B \ A).card ≤ r)
    (separated : ∀ u ∈ A \ B, ∀ v ∈ B \ A, ¬H.Adj u v)
    (bound : cost (x ∘ f) (A ∩ B) ≤ 4 * ρ * A.card * B.card / γ) :
    ∃ A' B' : Finset (Fin n), A' ∪ B' = R ∧ B'.Nonempty ∧ 2 * (B' \ A').card ≤ R.card ∧
      (∀ u ∈ A' \ B', ∀ v ∈ B' \ A', ¬G.Adj u v) ∧
      cost x (A' ∩ B') ≤ 4 * ρ * A'.card * B'.card / γ := by
  classical
  have hcard (S : Finset (Fin r)) : (S.image f).card = S.card :=
    Finset.card_image_of_injective _ f.injective
  have hR : R.card = r := by
    rw [← onto, hcard, Finset.card_univ, Fintype.card_fin]
  refine ⟨A.image f, B.image f, ?_, nonempty.image f, ?_, ?_, ?_⟩
  · rw [← Finset.image_union, cover, onto]
  · rw [← Finset.image_sdiff B A f.injective, hcard, hR]
    exact small
  · intro u hu v hv hadj
    rw [← Finset.image_sdiff A B f.injective] at hu
    rw [← Finset.image_sdiff B A f.injective] at hv
    obtain ⟨a, ha, heu⟩ := Finset.mem_image.mp hu
    obtain ⟨b, hb, hev⟩ := Finset.mem_image.mp hv
    exact separated a ha b hb (f.map_adj_iff.mp (by rw [heu, hev]; exact hadj))
  · rw [← Finset.image_inter A B f.injective, hcard, hcard]
    unfold cost
    rw [Finset.sum_image (fun _ _ _ _ h => f.injective h)]
    exact bound

theorem remainder_scale (n r ℓ : ℕ) (hn : 0 < n) (hℓ : 0 < ℓ)
    (k : ℝ) (hk : 0 < k) (large : 2 * n < 3 * r) :
    0 < (ℓ : ℝ) * (n : ℝ) ^ 2 / (3 * k) ∧
      ((ℓ : ℝ) * (n : ℝ) ^ 2 / (3 * k)) * k ≤ (ℓ : ℝ) * (r : ℝ) ^ 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hℓ' : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hr' : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hlarge : 2 * (n : ℝ) < 3 * (r : ℝ) := by exact_mod_cast large
  have hs : (n : ℝ) ^ 2 ≤ 3 * (r : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (le_of_lt (sub_pos.mpr hlarge)) (show 0 ≤ 3 * (r : ℝ) + 2 * n by positivity)]
  refine ⟨by positivity, ?_⟩
  have heq : ((ℓ : ℝ) * (n : ℝ) ^ 2 / (3 * k)) * k = (ℓ : ℝ) * (n : ℝ) ^ 2 / 3 := by
    field_simp
  rw [heq]
  nlinarith [mul_le_mul_of_nonneg_left hs hℓ'.le]


theorem power_light_separator (C : GraphClass) (hereditary : IsHereditary C)
    (a A : ℕ) (ha : 0 < a) (hA : 0 < A) (class_bound : HasPowerBagBound C a A) :
    ∃ K B : ℕ, 0 < K ∧ 0 < B ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G ∈ C n → 0 < n → ∀ (x : Fin n → ℚ≥0) (k p δ : ℝ) (ℓ : ℕ),
      0 < k → 0 < p → 0 < δ → 0 < ℓ →
      (∀ v, (x v : ℝ) ≤ 1) → (∑ v, (x v : ℝ)) ≤ k →
      edgeCost G (fun v => (x v : ℝ)) ≤ k ^ 2 / p →
      12 * (B : ℝ) * ((Nat.log2 (2 * n) : ℝ) + 1) ≤ δ * ℓ →
      (K : ℝ) * ((ℓ : ℝ) + 1) ^ (4 * a + 2) ≤ k →
      (2 * K : ℝ) * ((ℓ : ℝ) + 1) ^ (4 * a + 2) ≤ p →
      ∃ q, ∃ T : Lax263307.CutTraces.Trace G Finset.univ q,
        q ≤ n ∧ IsBalancedSeparator G (Lax263307.CutTraces.separator T) ∧
          cost (fun v => (x v : ℝ)) (Lax263307.CutTraces.separator T) ≤ δ * k := by
  classical
  obtain ⟨K, hK, hforced⟩ := Lax263307.ForcedSeparation.certificate_separation C hereditary a A ha hA class_bound
  obtain ⟨solve, c, _hpoly, hc, hsolve⟩ := Lax263307.VertexSplitting.split_certificate
  obtain ⟨B, hB, hratio⟩ := bounded_ratio c hc
  refine ⟨K, B, hK, hB, ?_⟩
  intro n G _ hG hn x k p δ ℓ hk hp _hδ hℓ hx hmass hedge hbudget htarget hsparsity
  let ρ : ℝ := B * ((Nat.log2 (2 * n) : ℝ) + 1)
  let γ : ℝ := (ℓ : ℝ) * (n : ℝ) ^ 2 / (3 * k)
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hγ : 0 < γ := (remainder_scale n n ℓ hn hℓ k hk (by omega)).1
  have hxnonnegative (v : Fin n) : 0 ≤ (x v : ℝ) := by positivity
  have horacle : ∀ R : Finset (Fin n), 2 * n < 3 * R.card →
      ∃ A' B' : Finset (Fin n), A' ∪ B' = R ∧ B'.Nonempty ∧ 2 * (B' \ A').card ≤ R.card ∧
        (∀ u ∈ A' \ B', ∀ v ∈ B' \ A', ¬G.Adj u v) ∧
        cost (fun v => (x v : ℝ)) (A' ∩ B') ≤ 4 * ρ * A'.card * B'.card / γ := by
    intro R hlargeR
    let V := ↥(↑R : Set (Fin n))
    let r := Fintype.card V
    let e : V ≃ Fin r := Fintype.equivFin V
    let H := (G.induce (↑R : Set (Fin n))).comap e.symm
    let f : H ↪g G := {
      toFun := fun v => (e.symm v).val
      inj' := fun u v h => e.symm.injective (Subtype.ext h)
      map_rel_iff' := Iff.rfl }
    have hr : r = R.card := Fintype.card_coe _
    have hrpos : 0 < r := by rw [hr]; omega
    have hrn : r ≤ n := by
      rw [hr]
      exact R.card_le_univ.trans_eq (Fintype.card_fin n)
    have hH := hereditary r n H G hG ⟨f⟩
    let y (v : Fin r) : ℚ≥0 := x (f v)
    let large : ℚ≥0 := (Nat.ceil (ρ * (2 * r : ℕ) ^ 2 / γ) + 1 : ℕ)
    have hlarge : ρ * (2 * r : ℕ) ^ 2 / γ < (large : ℝ) := by
      have h := Nat.le_ceil (ρ * (2 * r : ℕ) ^ 2 / γ)
      simp only [large]
      norm_cast at h ⊢
      simp only [Nat.cast_add, Nat.cast_one]
      linarith
    obtain ⟨cert, _encoded, hadmissible, hflow, hcut⟩ := hsolve r H y large hrpos
    have hcut' : (ratioCost (splitInstance H y large).network
        (splitInstance H y large).weights cert.cut : ℝ) ≤ ρ * (cert.flow.value : ℝ) :=
      hcut.trans (mul_le_mul_of_nonneg_right (hratio n r hrpos hrn) (by positivity))
    have hscale : γ * k ≤ (ℓ : ℝ) * (r : ℝ) ^ 2 :=
      (remainder_scale n r ℓ hn hℓ k hk (by rw [hr]; exact hlargeR)).2
    have hmass' : (∑ v : Fin r, (y v : ℝ)) ≤ k :=
      (sum_embedding f.toEmbedding (fun v => (x v : ℝ)) hxnonnegative).trans hmass
    have hedge' : edgeCost H (fun v => (y v : ℝ)) ≤ k ^ 2 / p :=
      (edge_cost_embedding H G f (fun v => (x v : ℝ)) hxnonnegative).trans hedge
    obtain ⟨hleft, hright, hcover, hseparated, hcost⟩ :=
      hforced r H hH hrpos y large cert ρ γ k p ℓ hℓ hρ hγ hk hp hscale
        (fun v => hx (f v)) hmass' hedge' htarget hsparsity hadmissible hflow hcut' hlarge
    obtain ⟨left, right, hcover', hright', hsmall, hsep', hcost'⟩ :=
      orient H (fun v => (y v : ℝ)) ρ γ (leftShore cert.cut) (rightShore cert.cut)
        hleft hright hcover hseparated hcost
    have honto : Finset.univ.image f = R := by
      ext v
      constructor
      · intro hv
        obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hv
        exact (e.symm u).property
      · intro hv
        exact Finset.mem_image.mpr ⟨e ⟨v, hv⟩, Finset.mem_univ _, by change (e.symm (e ⟨v, hv⟩)).val = v; rw [e.symm_apply_apply]⟩
    exact project_cut H G f R honto (fun v => (x v : ℝ)) ρ γ left right
      hcover' hright' hsmall hsep' hcost'
  obtain ⟨q, T, hq, hbalanced, hcost⟩ :=
    Lax263307.CutTraces.light_separator_from_oracle G (fun v => (x v : ℝ)) hxnonnegative ρ γ hρ hγ horacle
  refine ⟨q, T, hq, hbalanced, hcost.trans ?_⟩
  have hℓ' : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have heq : 4 * ρ * (n : ℝ) ^ 2 / γ = 12 * ρ * k / ℓ := by
    dsimp [γ]
    field_simp
    ring
  rw [heq]
  apply (div_le_iff₀ hℓ').mpr
  have hbudget' : 12 * ρ ≤ δ * ℓ := by dsimp [ρ]; nlinarith [hbudget]
  nlinarith [mul_le_mul_of_nonneg_right hbudget' hk.le]




/--
---
conclusion: Lax263307.LightSeparators.class_light_separator
---
Derive the integer power bag bound from the original separator hypothesis.
On every remainder larger than two thirds of the original graph, apply the
registered split solver and rule out its high-flow branch. Labeling preserves
shore sizes and costs; orient the cut to discard the smaller exclusive piece.
The repeated-cut theorem gives a balanced separator, and the global load
scale converts its cumulative cost bound into delta*k.
-/
theorem class_light_separator (C : GraphClass) (hereditary : IsHereditary C)
    (separators : HasStronglyEdgeSublinearSeparators C) :
    ∃ a K B : ℕ, 0 < a ∧ 0 < K ∧ 0 < B ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G ∈ C n → 0 < n → ∀ (x : Fin n → ℚ≥0) (k p δ : ℝ) (ℓ : ℕ),
      0 < k → 0 < p → 0 < δ → 0 < ℓ →
      (∀ v, (x v : ℝ) ≤ 1) → (∑ v, (x v : ℝ)) ≤ k →
      edgeCost G (fun v => (x v : ℝ)) ≤ k ^ 2 / p →
      12 * (B : ℝ) * ((Nat.log2 (2 * n) : ℝ) + 1) ≤ δ * ℓ →
      (K : ℝ) * ((ℓ : ℝ) + 1) ^ (4 * a + 2) ≤ k →
      (2 * K : ℝ) * ((ℓ : ℝ) + 1) ^ (4 * a + 2) ≤ p →
      ∃ q, ∃ T : Lax263307.CutTraces.Trace G Finset.univ q,
        q ≤ n ∧ IsBalancedSeparator G (Lax263307.CutTraces.separator T) ∧
          cost (fun v => (x v : ℝ)) (Lax263307.CutTraces.separator T) ≤ δ * k := by
  obtain ⟨a, A, ha, hA, hbound⟩ := Lax263307.EdgeBagBounds.power_bag_bound C hereditary separators
  obtain ⟨K, B, hK, hB, hlight⟩ := power_light_separator C hereditary a A ha hA hbound
  exact ⟨a, K, B, ha, hK, hB, hlight⟩

end Lax263307Proofs.LightSeparators
