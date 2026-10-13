import Lax263307Proofs.SeparatorDecompositions
import Lax263307.EdgeBagBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Lax263307Proofs.EdgeBagBounds

theorem log2_le_log (n : ℕ) :
    (Nat.log2 n : ℝ) ≤ Real.log ((n : ℝ) + 1) / Real.log 2 := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp : (2 : ℝ) ^ Nat.log2 n ≤ (n : ℝ) + 1 := by
    by_cases hn : n = 0
    · simp [hn]
    · have h := Nat.pow_log_le_self 2 hn
      rw [← Nat.log2_eq_log_two] at h
      have hh : (2 : ℝ) ^ Nat.log2 n ≤ n := by exact_mod_cast h
      linarith
  have h := Real.log_le_log (by positivity) hp
  rw [Real.log_pow] at h
  exact (le_div_iff₀ htwo).mpr h

theorem depth_absorb (ε : ℝ) (hε : 0 < ε) (n m : ℕ) (order_bound : n ≤ 2 * m) :
    (Lax263307.RecursionDepth.depth n + 1 : ℝ) ≤
      (2 / (ε * Real.log 2) + 5) * Real.rpow ((m : ℝ) + 1) ε := by
  let z : ℝ := m + 1
  have hz : 1 ≤ z := by dsimp [z]; exact le_add_of_nonneg_left (Nat.cast_nonneg m)
  have hp : 1 ≤ Real.rpow z ε := Real.one_le_rpow hz hε.le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log ((n : ℝ) + 1) ≤ Real.log (2 * z) :=
    Real.log_le_log (by positivity) (by dsimp [z]; exact_mod_cast (show n + 1 ≤ 2 * (m + 1) by omega))
  have hsplit : Real.log (2 * z) = Real.log 2 + Real.log z :=
    Real.log_mul (by norm_num) (by linarith)
  have hdr : (Lax263307.RecursionDepth.depth n : ℝ) ≤ 2 * ((Nat.log2 n : ℝ) + 1) := by
    exact_mod_cast Lax263307.RecursionDepth.logarithmic_bound n
  have hnat := log2_le_log n
  have hsmall := Real.log_le_rpow_div (show 0 ≤ z by linarith) hε
  have htop : Real.log ((n : ℝ) + 1) ≤ Real.log 2 + Real.rpow z ε / ε :=
    hlog.trans (hsplit.le.trans (add_le_add_right hsmall _))
  have hnat' : (Nat.log2 n : ℝ) ≤ 1 + Real.rpow z ε / (ε * Real.log 2) := by
    apply hnat.trans
    calc
      _ ≤ (Real.log 2 + Real.rpow z ε / ε) / Real.log 2 :=
        div_le_div_of_nonneg_right htop hlog2.le
      _ = _ := by field_simp
  have heq : (2 / (ε * Real.log 2) + 5) * Real.rpow z ε =
      2 * (Real.rpow z ε / (ε * Real.log 2)) + 5 * Real.rpow z ε := by ring
  change (Lax263307.RecursionDepth.depth n : ℝ) + 1 ≤ _
  rw [heq]
  linarith


open Lax263307.GraphClasses Lax263307.EdgeSublinearSeparators Lax228581.Treewidth

theorem edge_order_bound (C : GraphClass) (hereditary : IsHereditary C)
    (B : ℕ → ℕ) (monotone : Monotone B) (positive : ∀ m, 1 ≤ B m)
    (separators : ∀ n (G : SimpleGraph (Fin n)), G ∈ C n →
      ∃ S : Finset (Fin n), IsBalancedSeparator G S ∧ S.card ≤ B G.edgeSet.ncard)
    {n : ℕ} (G : SimpleGraph (Fin n)) (member : G ∈ C n) :
    ∃ r : ℕ, r ≤ 2 * G.edgeSet.ncard ∧ ∃ D : TreeDecomposition G, ∀ j,
      (D.bag j).card ≤ B G.edgeSet.ncard * (Lax263307.RecursionDepth.depth r + 1) := by
  classical
  let U := Finset.univ.filter (fun v => 0 < G.degree v)
  have hU : U.card ≤ 2 * G.edgeSet.ncard := by
    have hsum : (∑ v : Fin n, if 0 < G.degree v then 1 else 0) ≤ ∑ v : Fin n, G.degree v := by
      apply Finset.sum_le_sum
      intro v _
      split_ifs <;> omega
    rw [G.sum_degrees_eq_twice_card_edges, G.edgeFinset_card, Set.fintypeCard_eq_ncard] at hsum
    simpa [U] using hsum
  let V := ↥(↑U : Set (Fin n))
  let r := Fintype.card V
  let e : V ≃ Fin r := Fintype.equivFin V
  let H := (G.induce (↑U : Set (Fin n))).comap e.symm
  let f : H ↪g G := {
    toFun := fun v => (e.symm v).val
    inj' := fun a b h => e.symm.injective (Subtype.ext h)
    map_rel_iff' := Iff.rfl }
  have hH := hereditary r n H G member ⟨f⟩
  obtain ⟨D, hD⟩ := Lax263307.SeparatorDecompositions.recursive_bag_bound C hereditary B monotone positive separators H hH
  let g : (G.induce (↑U : Set (Fin n))) ↪g H := {
    toFun := e
    inj' := e.injective
    map_rel_iff' := by intro a b; simp [H] }
  let E := Lax263307Proofs.TreeExtensions.pullback g D
  have hB : 1 ≤ B G.edgeSet.ncard * (Lax263307.RecursionDepth.depth r + 1) :=
    by have := positive G.edgeSet.ncard; nlinarith
  have hE (j : E.Node) : (E.bag j).card ≤ B G.edgeSet.ncard * (Lax263307.RecursionDepth.depth r + 1) :=
    (Lax263307Proofs.TreeExtensions.pullback_card g D j).trans ((hD j).trans
      (Nat.mul_le_mul_right _ (monotone (Lax263307Proofs.SeparatorDecompositions.embedding_edge_bound f))))
  have isolated (v : Fin n) (hv : v ∉ (↑U : Set (Fin n))) : G.IsIsolated v := by
    have hz : G.degree v = 0 := by
      have hnot : ¬0 < G.degree v := by simpa [U] using hv
      omega
    intro u hu
    exact (G.degree_eq_zero v).mp hz u hu
  refine ⟨r, ?_, Lax263307Proofs.TreeExtensions.extendIsolated (G := G) (↑U) isolated E,
    Lax263307Proofs.TreeExtensions.extendIsolated_card (G := G) (↑U) isolated E _ hB hE⟩
  have hr : r = U.card := Fintype.card_coe _
  rw [hr]
  exact hU


/--
---
conclusion: Lax263307.EdgeBagBounds.sublinear_bag_bound
---
Round separator sizes up to a monotone positive integer bound, and recurse
on balanced components. Delete isolated vertices first so the recursive
order is at most twice the edge count, then restore their singleton bags.
The inequality log x ≤ x^epsilon/epsilon absorbs depth at exponent
beta=(1+b)/2, still below one.
-/
theorem sublinear_bag_bound (C : GraphClass) (hereditary : IsHereditary C)
    (separators : HasStronglyEdgeSublinearSeparators C) :
    ∃ β c : ℝ, 0 ≤ β ∧ β < 1 ∧ 0 < c ∧ ∀ n (G : SimpleGraph (Fin n)), G ∈ C n →
      ∃ D : TreeDecomposition G, ∀ j,
        ((D.bag j).card : ℝ) ≤ c * Real.rpow ((G.edgeSet.ncard : ℝ) + 1) β := by
  classical
  obtain ⟨b, c, hb, hb1, hc, hsep⟩ := separators
  let ε := (1 - b) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  let B (m : ℕ) := Nat.ceil (c * Real.rpow ((m : ℝ) + 1) b)
  have hmono : Monotone B := by
    intro m t hmt
    apply Nat.ceil_mono
    apply mul_le_mul_of_nonneg_left _ hc.le
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.add_le_add_right hmt 1) hb
  have hpos (m : ℕ) : 1 ≤ B m := by
    apply Nat.one_le_ceil_iff.mpr
    exact mul_pos hc (Real.rpow_pos_of_pos (by positivity) b)
  have hseps : ∀ n (G : SimpleGraph (Fin n)), G ∈ C n →
      ∃ S : Finset (Fin n), IsBalancedSeparator G S ∧ S.card ≤ B G.edgeSet.ncard := by
    intro n G hG
    obtain ⟨S, hS, hcost⟩ := hsep n G hG
    exact ⟨S, hS, Nat.cast_le.mp (hcost.trans (Nat.le_ceil _))⟩
  have hDpos : 0 < 2 / (ε * Real.log 2) + 5 := by
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  refine ⟨b + ε, (c + 1) * (2 / (ε * Real.log 2) + 5), by dsimp [ε]; linarith,
    by dsimp [ε]; linarith, mul_pos (by linarith) hDpos, ?_⟩
  intro n G hG
  obtain ⟨r, hr, D, hD⟩ := edge_order_bound C hereditary B hmono hpos hseps G hG
  refine ⟨D, fun j => ?_⟩
  let m := G.edgeSet.ncard
  have hpow : 1 ≤ Real.rpow ((m : ℝ) + 1) b := Real.one_le_rpow (by have := Nat.cast_nonneg m (α := ℝ); linarith) hb
  have hB : (B m : ℝ) ≤ (c + 1) * Real.rpow ((m : ℝ) + 1) b := by
    have hceil := (Nat.ceil_lt_add_one (show 0 ≤ c * Real.rpow ((m : ℝ) + 1) b by positivity)).le
    change (Nat.ceil (c * Real.rpow ((m : ℝ) + 1) b) : ℝ) ≤ _
    nlinarith
  have hdr := depth_absorb ε hε r m hr
  have hj : ((D.bag j).card : ℝ) ≤ (B m : ℝ) * (Lax263307.RecursionDepth.depth r + 1) := by
    exact_mod_cast hD j
  calc
    _ ≤ (B m : ℝ) * (Lax263307.RecursionDepth.depth r + 1) := hj
    _ ≤ ((c + 1) * Real.rpow ((m : ℝ) + 1) b) *
        ((2 / (ε * Real.log 2) + 5) * Real.rpow ((m : ℝ) + 1) ε) :=
      mul_le_mul hB hdr (by positivity) (by positivity)
    _ = _ := by
      have hpower : Real.rpow ((m : ℝ) + 1) (b + ε) =
          Real.rpow ((m : ℝ) + 1) b * Real.rpow ((m : ℝ) + 1) ε :=
        Real.rpow_add (by positivity) b ε
      change _ = (c + 1) * (2 / (ε * Real.log 2) + 5) * Real.rpow ((m : ℝ) + 1) (b + ε)
      rw [hpower]
      ring




/--
---
conclusion: Lax263307.EdgeBagBounds.power_bag_bound
---
Choose a positive integer a with a(1-beta)>1. Raise the sublinear bag
bound to its a-th power, enlarge the constant to a positive integer A,
and use a*beta≤a-1 and m+1≥1 to bound the remaining real power.
-/
theorem power_bag_bound (C : GraphClass) (hereditary : IsHereditary C)
    (separators : HasStronglyEdgeSublinearSeparators C) :
    ∃ a A : ℕ, 0 < a ∧ 0 < A ∧ Lax263307.PowerBagBounds.HasPowerBagBound C a A := by
  obtain ⟨β, c, _hβ, hβ1, hc, hbags⟩ := sublinear_bag_bound C hereditary separators
  have hgap : 0 < 1 - β := by linarith
  obtain ⟨a, ha⟩ := exists_nat_gt (1 / (1 - β))
  have hap : 0 < a := by
    have hi : 0 < 1 / (1 - β) := div_pos zero_lt_one hgap
    have : (0 : ℝ) < a := hi.trans ha
    exact_mod_cast this
  have hexp : β * (a : ℝ) ≤ (a - 1 : ℕ) := by
    have hg : 1 < (a : ℝ) * (1 - β) := (div_lt_iff₀ hgap).mp ha
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    nlinarith
  let A := Nat.ceil (c ^ a) + 1
  have hA : c ^ a ≤ (A : ℝ) := by
    have h := Nat.le_ceil (c ^ a)
    simp only [A, Nat.cast_add, Nat.cast_one]
    linarith
  refine ⟨a, A, hap, by dsimp [A]; omega, ?_⟩
  intro n G hG
  obtain ⟨D, hD⟩ := hbags n G hG
  refine ⟨D, fun j => ?_⟩
  let m := G.edgeSet.ncard
  have hm : 1 ≤ (m : ℝ) + 1 := by have := Nat.cast_nonneg m (α := ℝ); linarith
  have hj : ((D.bag j).card : ℝ) ^ a ≤ (A : ℝ) * ((m : ℝ) + 1) ^ (a - 1) := by
    calc
      _ ≤ (c * Real.rpow ((m : ℝ) + 1) β) ^ a :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (hD j) a
      _ = c ^ a * Real.rpow ((m : ℝ) + 1) (β * (a : ℝ)) := by
        rw [mul_pow]
        have hp : Real.rpow ((m : ℝ) + 1) (β * (a : ℝ)) =
            Real.rpow ((m : ℝ) + 1) β ^ a := Real.rpow_mul_natCast (by linarith) β a
        rw [hp]
      _ ≤ (A : ℝ) * Real.rpow ((m : ℝ) + 1) (a - 1 : ℕ) :=
        mul_le_mul hA (Real.rpow_le_rpow_of_exponent_le hm hexp) (Real.rpow_nonneg (by linarith) _) (Nat.cast_nonneg A)
      _ = _ := by rw [Real.rpow_eq_pow, Real.rpow_natCast]
  exact_mod_cast hj

end Lax263307Proofs.EdgeBagBounds
