import Lax263307.CoupledRouteSampling
import Lax263307Proofs.FiniteProductSampling
import Mathlib.Tactic

namespace Lax263307Proofs.CoupledRouteSampling


open Lax263307.RouteDistributions Lax263307.ConditionalRoutes
open Lax263307.FiniteProductSampling
open Lax263307Proofs.FiniteProductSampling (single_marginal pair_marginal)
open Lax263307.CoupledRouteSampling

theorem uniform_mass {n : ℕ} (hn : 0 < n) : (∑ x, uniformWeight n x) = 1 := by
  simp [uniformWeight]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  field_simp

/--
---
conclusion: Lax263307.CoupledRouteSampling.joint_normalized
---
For each fixed vertex assignment, conditional edge routes form a
normalized product law. Sum them out, then sum the uniform vertex law.
-/
theorem joint_normalized {n q t m : ℕ} {G : SimpleGraph (Fin n)}
    (D : Distribution G q) (hn : 0 < n) (a b : Fin m → Fin t) :
    (∀ φ ψ, 0 ≤ jointWeight D a b φ ψ) ∧
      (∑ φ, ∑ ψ, jointWeight D a b φ ψ) = 1 := by
  classical
  have hcond (φ : Fin t → Fin n) (e : Fin m) := conditional_correct D hn (φ (a e)) (φ (b e))
  refine ⟨?_, ?_⟩
  · intro φ ψ
    apply mul_nonneg
    · apply Finset.prod_nonneg
      intro e _
      exact div_nonneg zero_le_one (by positivity)
    · apply Finset.prod_nonneg
      intro e _
      exact (hcond φ e).1 _
  · unfold jointWeight
    simp_rw [← Finset.mul_sum, normalized _ (fun e => (hcond _ e).2.1), mul_one]
    exact normalized _ (fun _ => uniform_mass hn)

/--
---
conclusion: Lax263307.CoupledRouteSampling.joint_valid
---
Positive joint probability forces positive conditional probability
for every edge. Conditional support fixes endpoints and gives simple
graph routes.
-/
theorem joint_valid {n q t m : ℕ} {G : SimpleGraph (Fin n)}
    (D : Distribution G q) (hn : 0 < n) (a b : Fin m → Fin t)
    (φ : Fin t → Fin n) (ψ : Fin m → Fin q) (positive : 0 < jointWeight D a b φ ψ) :
    ∀ e, (D.route (ψ e)).head? = some (φ (a e)) ∧
      (D.route (ψ e)).getLast? = some (φ (b e)) ∧
      (D.route (ψ e)).Nodup ∧ (D.route (ψ e)).IsChain G.Adj := by
  classical
  intro e
  have hprod : weight (fun e => conditional D (φ (a e)) (φ (b e))) ψ ≠ 0 :=
    (mul_ne_zero_iff.mp (ne_of_gt positive)).2
  have he : conditional D (φ (a e)) (φ (b e)) (ψ e) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hprod e (Finset.mem_univ _)
  have hc := conditional_correct D hn (φ (a e)) (φ (b e))
  exact hc.2.2 (ψ e) (lt_of_le_of_ne (hc.1 _) (Ne.symm he))

theorem sum_two {κ : Type*} [Fintype κ] (h : (Fin 2 → κ) → ℝ) :
    (∑ ψ, h ψ) = ∑ u, ∑ v, h ![u, v] := by
  rw [← (finTwoArrowEquiv κ).symm.sum_comp h]
  simp only [Fintype.sum_prod_type]
  rfl

/--
---
conclusion: Lax263307.CoupledRouteSampling.single_edge_law
---
First sum out all other edge routes. Restrict the uniform vertex
assignment to the two distinct edge endpoints, then use the conditional
mixture identity.
-/
theorem single_edge_law {n q t m : ℕ} {G : SimpleGraph (Fin n)}
    (D : Distribution G q) (hn : 0 < n) (a b : Fin m → Fin t)
    (e : Fin m) (nonloop : a e ≠ b e) (i : Fin q) :
    (∑ φ, ∑ ψ, jointWeight D a b φ ψ * (if ψ e = i then (1 : ℝ) else 0)) =
      D.probability i := by
  classical
  have hinner (φ : Fin t → Fin n) :
      (∑ ψ, jointWeight D a b φ ψ * (if ψ e = i then (1 : ℝ) else 0)) =
      weight (fun _ : Fin t => uniformWeight n) φ * conditional D (φ (a e)) (φ (b e)) i := by
    unfold jointWeight
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    rw [single_marginal _ (fun c => (conditional_correct D hn _ _).2.1) e
      (fun x => if x = i then (1 : ℝ) else 0)]
    simp
  simp_rw [hinner]
  let j : Fin 2 ↪ Fin t := ⟨![a e, b e], by
    intro u v huv
    fin_cases u <;> fin_cases v <;> simp_all⟩
  have hp := embedding_marginal (fun _ : Fin t => uniformWeight n)
    (fun _ => uniform_mass hn) j (fun ψ => conditional D (ψ 0) (ψ 1) i)
  change (∑ φ, weight (fun _ : Fin t => uniformWeight n) φ *
    conditional D (φ (a e)) (φ (b e)) i) = _ at hp
  rw [hp, sum_two]
  simp only [weight, Fin.prod_univ_two, uniformWeight, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hm := mixture_identity D i
  simp_rw [← Finset.mul_sum]
  rw [hm]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  field_simp

theorem sum_four {κ : Type*} [Fintype κ] (h : (Fin 4 → κ) → ℝ) :
    (∑ ψ, h ψ) = ∑ u, ∑ v, ∑ s, ∑ t, h ![u, v, s, t] := by
  let e : (κ × κ) × (κ × κ) ≃ (Fin 4 → κ) :=
    (Equiv.prodCongr (finTwoArrowEquiv κ).symm (finTwoArrowEquiv κ).symm).trans (Fin.appendEquiv 2 2)
  have he (u v s t : κ) : e ((u, v), (s, t)) = ![u, v, s, t] := by
    funext i
    fin_cases i <;> rfl
  rw [← e.sum_comp h]
  simp only [Fintype.sum_prod_type]
  simp_rw [he]

/--
---
conclusion: Lax263307.CoupledRouteSampling.nonincident_edge_law
---
Sum out all other edge routes. Restrict the uniform vertex assignment
to the four distinct endpoints, then apply the independent endpoint
mixture identity.
-/
theorem nonincident_edge_law {n q t m : ℕ} {G : SimpleGraph (Fin n)}
    (D : Distribution G q) (hn : 0 < n) (a b : Fin m → Fin t)
    (e f : Fin m) (nonincident : Function.Injective ![a e, b e, a f, b f]) (i j : Fin q) :
    (∑ φ, ∑ ψ, jointWeight D a b φ ψ *
      ((if ψ e = i then (1 : ℝ) else 0) * (if ψ f = j then (1 : ℝ) else 0))) =
      D.probability i * D.probability j := by
  classical
  have hef : e ≠ f := by
    intro h
    have hi : (0 : Fin 4) = 2 := nonincident (by simp [h])
    exact (by decide : (0 : Fin 4) ≠ 2) hi
  have hinner (φ : Fin t → Fin n) :
      (∑ ψ, jointWeight D a b φ ψ *
        ((if ψ e = i then (1 : ℝ) else 0) * (if ψ f = j then (1 : ℝ) else 0))) =
      weight (fun _ : Fin t => uniformWeight n) φ *
        (conditional D (φ (a e)) (φ (b e)) i * conditional D (φ (a f)) (φ (b f)) j) := by
    unfold jointWeight
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    rw [pair_marginal _ (fun c => (conditional_correct D hn _ _).2.1) e f hef
      (fun x => if x = i then (1 : ℝ) else 0) (fun x => if x = j then (1 : ℝ) else 0)]
    simp
  simp_rw [hinner]
  let J : Fin 4 ↪ Fin t := ⟨![a e, b e, a f, b f], nonincident⟩
  have hp := embedding_marginal (fun _ : Fin t => uniformWeight n)
    (fun _ => uniform_mass hn) J (fun ψ => conditional D (ψ 0) (ψ 1) i * conditional D (ψ 2) (ψ 3) j)
  change (∑ φ, weight (fun _ : Fin t => uniformWeight n) φ *
    (conditional D (φ (a e)) (φ (b e)) i * conditional D (φ (a f)) (φ (b f)) j)) = _ at hp
  rw [hp, sum_four]
  simp only [weight, uniformWeight, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
  have hterm (u v s t : Fin n) :
      (1 / (n : ℝ)) ^ 4 * (conditional D u v i * conditional D s t j) =
      conditional D u v i * conditional D s t j / (n : ℝ) ^ 4 := by ring
  simp_rw [hterm]
  exact independent_pair_mixture D hn i j


end Lax263307Proofs.CoupledRouteSampling
