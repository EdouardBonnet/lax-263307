import Lax263307.FiniteProductSampling
import Mathlib.Tactic

namespace Lax263307Proofs.FiniteProductSampling

open Lax263307.FiniteProductSampling

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

/--
---
conclusion: Lax263307.FiniteProductSampling.normalized
---
Expand the sum over all assignments into a product of coordinate sums.
Every coordinate has mass one.
-/
theorem normalized (f : ι → κ → ℝ) (mass : ∀ a, (∑ x, f a x) = 1) :
    (∑ φ : ι → κ, weight f φ) = 1 := by
  classical
  unfold weight
  rw [← Fintype.prod_sum]
  simp only [mass, Finset.prod_const_one]

theorem feature_marginal (f : ι → κ → ℝ) (mass : ∀ a, (∑ x, f a x) = 1)
    (S : Finset ι) (g : ι → κ → ℝ) :
    (∑ φ : ι → κ, weight f φ * ∏ a ∈ S, g a (φ a)) =
      ∏ a ∈ S, ∑ x, f a x * g a x := by
  classical
  have hterm (φ : ι → κ) : weight f φ * (∏ a ∈ S, g a (φ a)) =
      ∏ a, f a (φ a) * (if a ∈ S then g a (φ a) else 1) := by
    rw [Finset.prod_mul_distrib, Fintype.prod_ite_mem]
    rfl
  simp_rw [hterm]
  rw [← Fintype.prod_sum (fun a x => f a x * (if a ∈ S then g a x else 1))]
  have hfactor (a : ι) :
      (∑ x, f a x * (if a ∈ S then g a x else 1)) =
      if a ∈ S then (∑ x, f a x * g a x) else 1 := by
    by_cases ha : a ∈ S
    · simp [ha]
    · simp [ha, mass a]
  simp_rw [hfactor]
  exact Fintype.prod_ite_mem S _

theorem single_marginal (f : ι → κ → ℝ) (mass : ∀ a, (∑ x, f a x) = 1)
    (a : ι) (g : κ → ℝ) :
    (∑ φ : ι → κ, weight f φ * g (φ a)) = ∑ x, f a x * g x := by
  classical
  simpa using feature_marginal f mass {a} (fun _ x => g x)

theorem pair_marginal (f : ι → κ → ℝ) (mass : ∀ a, (∑ x, f a x) = 1)
    (a b : ι) (different : a ≠ b) (g h : κ → ℝ) :
    (∑ φ : ι → κ, weight f φ * (g (φ a) * h (φ b))) =
      (∑ x, f a x * g x) * (∑ x, f b x * h x) := by
  classical
  have heq (φ : ι → κ) : (∏ c ∈ ({a, b} : Finset ι),
      if c = a then g (φ c) else h (φ c)) = g (φ a) * h (φ b) := by
    simp [different, Ne.symm different]
  have hm := feature_marginal f mass {a, b} (fun c x => if c = a then g x else h x)
  simp_rw [heq] at hm
  simpa [different, Ne.symm different] using hm

theorem restriction_marginal (f : ι → κ → ℝ) (mass : ∀ a, (∑ x, f a x) = 1)
    (S : Finset ι) (H : (↥S → κ) → ℝ) :
    (∑ φ : ι → κ, weight f φ * H (fun a : ↥S => φ a)) =
      ∑ ψ : ↥S → κ, weight (fun a : ↥S => f a) ψ * H ψ := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun a : ι => a ∈ S) (fun _ => κ)
  have hsplit (ψ : ↥S → κ) (ξ : {a : ι // a ∉ S} → κ) :
      weight f (e.symm (ψ, ξ)) = weight (fun a : ↥S => f a) ψ *
        weight (fun a : {a : ι // a ∉ S} => f a) ξ := by
    unfold weight
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun a : ι => a ∈ S)]
    congr 1 <;> apply Finset.prod_congr (by ext; simp) <;> intro a _ <;>
      simp [e, Equiv.piEquivPiSubtypeProd, a.property]
  have heval (ψ : ↥S → κ) (ξ : {a : ι // a ∉ S} → κ) :
      (fun a : ↥S => e.symm (ψ, ξ) a) = ψ := by
    funext a
    simp [e, Equiv.piEquivPiSubtypeProd, a.property]
  rw [← e.symm.sum_comp (fun φ => weight f φ * H (fun a : ↥S => φ a))]
  simp only [Fintype.sum_prod_type]
  simp_rw [hsplit, heval]
  apply Finset.sum_congr rfl
  intro ψ _
  have hterm (ξ : {a : ι // a ∉ S} → κ) :
      weight (fun a : ↥S => f a) ψ * weight (fun a : {a : ι // a ∉ S} => f a) ξ * H ψ =
      (weight (fun a : ↥S => f a) ψ * H ψ) * weight (fun a : {a : ι // a ∉ S} => f a) ξ := by ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have hm := normalized (fun a : {a : ι // a ∉ S} => f a) (fun a => mass a)
  rw [hm, mul_one]

/--
---
conclusion: Lax263307.FiniteProductSampling.embedding_marginal
---
Split assignments into the selected coordinates and their complement.
Sum the complement product to one, then reindex selected coordinates
by the given embedding.
-/
theorem embedding_marginal {k : ℕ} (f : ι → κ → ℝ)
    (mass : ∀ a, (∑ x, f a x) = 1) (j : Fin k ↪ ι) (H : (Fin k → κ) → ℝ) :
    (∑ φ : ι → κ, weight f φ * H (fun a => φ (j a))) =
      ∑ ψ : Fin k → κ, weight (fun a => f (j a)) ψ * H ψ := by
  classical
  let S := Finset.univ.map j
  let a : Fin k → ↥S := fun b => ⟨j b, Finset.mem_map.mpr ⟨b, Finset.mem_univ _, rfl⟩⟩
  have ha : Function.Bijective a := by
    constructor
    · intro b c h
      exact j.injective (congrArg Subtype.val h)
    · rintro ⟨c, hc⟩
      obtain ⟨b, _, hb⟩ := Finset.mem_map.mp hc
      exact ⟨b, Subtype.ext hb⟩
  let e : Fin k ≃ ↥S := Equiv.ofBijective a ha
  let A : (Fin k → κ) ≃ (↥S → κ) := Equiv.arrowCongr e (Equiv.refl κ)
  have hev (ψ : Fin k → κ) (b : Fin k) : A ψ (e b) = ψ b := by simp [A]
  have hw (ψ : Fin k → κ) :
      weight (fun b : ↥S => f b) (A ψ) = weight (fun b => f (j b)) ψ := by
    unfold weight
    rw [← e.prod_comp (fun b : ↥S => f b (A ψ b))]
    apply Finset.prod_congr rfl
    intro b _
    rw [hev]
    rfl
  have h := restriction_marginal f mass S (fun ψ => H (fun b => ψ (a b)))
  change (∑ φ : ι → κ, weight f φ * H (fun b => φ (j b))) = _ at h
  rw [h]
  symm
  apply Fintype.sum_equiv A
  intro ψ
  rw [hw]
  congr 1
  apply congrArg H
  funext b
  exact (hev ψ b).symm


end Lax263307Proofs.FiniteProductSampling
