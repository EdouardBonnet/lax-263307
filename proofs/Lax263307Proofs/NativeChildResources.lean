import Lax263307Proofs.NearOracle

namespace Lax263307Proofs.NativeChildResources

open Lax263307 ComputedRounding

/-- A positive loss makes the rounded target fit inside the component.
The positivity of the cost matters: empty/light components are skipped. -/
theorem target_le (δ c : ℚ) (q : ℕ) (hδ : 0<δ) (hc : 0<c) (hq : c≤q) : target δ c≤q := by
  have hq0 : q≠0 := by intro he; subst q; norm_num at hq; linarith
  have hlt : (1-δ)*c<(q : ℚ) := by nlinarith
  have hfloor := (Nat.floor_lt' hq0).mpr hlt
  simpa only [target,Nat.add_one_le_iff] using hfloor

theorem component_cost_le {n : ℕ} (x : Fin n → ℚ≥0) (C : Finset (Fin n))
    (hx : ∀ v,x v≤1) : (∑ v∈C,(x v : ℚ))≤C.card := by
  calc
    _ ≤ ∑ _v∈C,(1 : ℚ) := Finset.sum_le_sum (fun v _ => by exact_mod_cast hx v)
    _ = _ := by simp

/-- The actual successful heavy search establishes the unit cost bound. -/
theorem selected_costs {n : ℕ} (a K b D k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (y : RationalConditioning.RationalVector n (AlgorithmParameters.level a K b n D))
    (hK : 0<K) (hb : 0<b) (hD : 4≤D) (hn : 0<n)
    (hlarge : AlgorithmParameters.cutoff a K b n D<k)
    (hy : LinearRelaxation.IsFeasible G k (AlgorithmParameters.level a K b n D)
      (RationalConditioning.realVector y)) (A : Finset (Fin n))
    (hfind : HeavyRationalConditioning.findHeavyConditioning G k
      (AlgorithmParameters.sparsity a K b n D) y=some A) :
    ∀ v, NearOracle.costs y A v≤1 := by
  have hbud := AlgorithmParameters.budgets hK hb hD hlarge
  obtain ⟨A',hfind',_,_,_,hcosts,_,_⟩ := HeavyRationalConditioning.search_correct G k
    (AlgorithmParameters.level a K b n D) (AlgorithmParameters.sparsity a K b n D) y hy hn
    (by omega) hbud.2.2.1 hbud.2.1 hbud.2.2.2.2.2.2.1
  have heq : A'=A := Option.some.inj (hfind'.symm.trans hfind)
  subst A'
  intro v
  have hreal : (NearOracle.costs y A v : ℝ)≤1 := by
    rw [Lax263307Proofs.NearOracle.costs_cast y A (fun v => (hcosts v).1) v]
    exact (hcosts v).2
  exact_mod_cast hreal

/-- Every actual heavy-child query has positive order and a target at most
that order. Thus exhaustive tables and masks use the same root workspace
budget even at the last recursion level. -/
theorem active_child {n : ℕ} (D k : ℕ) (x : Fin n → ℚ≥0) (C : Finset (Fin n))
    (hD : 0<D) (hx : ∀ v,x v≤1)
    (hactive : (1/(D : ℚ))*k/(4*(n : ℚ))<(∑ v∈C,(x v : ℚ))) :
    0<C.card ∧ target (1/(D : ℚ)) (∑ v∈C,(x v : ℚ))≤C.card ∧ C.card≤n := by
  have hδ : (0 : ℚ)<1/D := by positivity
  have hc : (0 : ℚ)<∑ v∈C,(x v : ℚ) := lt_of_le_of_lt (by positivity) hactive
  have hcost := component_cost_le x C hx
  have hpos : (0 : ℚ)<C.card := hc.trans_le hcost
  exact ⟨by exact_mod_cast hpos,target_le _ _ _ hδ hc hcost,
    C.card_le_univ.trans_eq (Fintype.card_fin n)⟩

end Lax263307Proofs.NativeChildResources
