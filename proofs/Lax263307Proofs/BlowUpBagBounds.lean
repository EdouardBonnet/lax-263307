import Lax263307Proofs.EdgeBagBounds
import Lax263307.BlowUpBagBounds
import Lax263307.BlowUpDeletion
import Mathlib.Logic.Equiv.Sum
import Mathlib.Tactic

namespace Lax263307Proofs.BlowUpBagBounds

open Lax263307.GraphClasses Lax263307.EdgeSublinearSeparators
open Lax263307.BlowUpClasses Lax263307.IndependentBlowUp Lax228581.Treewidth

/--
---
conclusion: Lax263307.BlowUpBagBounds.blowup_sublinear_bag_bound
---
Restrict the base graph to used projection fibres, retaining class membership.
One representative per fibre embeds it into the given blow-up and bounds
its edge count. Enumerate the fibres to form an explicit copy-graph
isomorphism. Apply degree-deletion optimization to its base decomposition
and pull the resulting bags through that isomorphism.
-/
theorem blowup_sublinear_bag_bound (C : GraphClass) (hereditary : IsHereditary C)
    (separators : HasStronglyEdgeSublinearSeparators C) :
    ∃ β c : ℝ, 0 ≤ β ∧ β < 1 ∧ 0 < c ∧ ∀ m (H : SimpleGraph (Fin m)), H ∈ blowUpClass C m →
      ∃ D : TreeDecomposition H, ∀ j,
        ((D.bag j).card : ℝ) ≤ c * Real.rpow ((H.edgeSet.ncard : ℝ) + 1) β := by
  classical
  obtain ⟨b, c, hb, hb1, hc, hbase⟩ := Lax263307.EdgeBagBounds.sublinear_bag_bound C hereditary separators
  refine ⟨(1 + b) / 2, 3 + 2 * (c + 2), by linarith, by linarith, by linarith, ?_⟩
  intro m H hH
  obtain ⟨n, G, hG, p, hAdj⟩ := hH
  let U := Finset.univ.image p
  let V := ↥(↑U : Set (Fin n))
  let r := Fintype.card V
  let e : V ≃ Fin r := Fintype.equivFin V
  let G₀ := G.comap (fun i : Fin r => (e.symm i).val)
  let f : G₀ ↪g G := {
    toFun := fun i => (e.symm i).val
    inj' := fun a b h => e.symm.injective (Subtype.ext h)
    map_rel_iff' := Iff.rfl }
  have hG₀ := hereditary r n G₀ G hG ⟨f⟩
  let q (u : Fin m) : Fin r := e ⟨p u, Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩⟩
  have hq (u : Fin m) : (e.symm (q u)).val = p u := by
    dsimp only [q]
    rw [e.symm_apply_apply]
  have hqsurj : Function.Surjective q := by
    intro i
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp (e.symm i).property
    refine ⟨u, e.symm.injective (Subtype.ext ?_)⟩
    rw [hq]
    exact hu
  have hAdj₀ (u v : Fin m) : H.Adj u v ↔ G₀.Adj (q u) (q v) := by
    change H.Adj u v ↔ G.Adj (e.symm (q u)).val (e.symm (q v)).val
    rw [hq, hq]
    exact hAdj u v
  let s (i : Fin r) := Classical.choose (hqsurj i)
  have hs (i : Fin r) : q (s i) = i := Classical.choose_spec (hqsurj i)
  let representative : G₀ ↪g H := {
    toFun := s
    inj' := (show Function.LeftInverse q s from hs).injective
    map_rel_iff' := by intro i j; change H.Adj (s i) (s j) ↔ G₀.Adj i j; rw [hAdj₀, hs, hs] }
  have hedge : G₀.edgeSet.ncard ≤ H.edgeSet.ncard :=
    Lax263307Proofs.SeparatorDecompositions.embedding_edge_bound representative
  let copies (i : Fin r) := Fintype.card {u : Fin m // q u = i}
  let label : Vertex copies ≃ Fin m :=
    (Equiv.sigmaCongrRight (fun i => (Fintype.equivFin {u : Fin m // q u = i}).symm)).trans
      (Equiv.sigmaFiberEquiv q)
  have hlabel (u : Vertex copies) : q (label u) = u.1 := by
    change q (((Fintype.equivFin {v : Fin m // q v = u.1}).symm u.2).val) = u.1
    exact ((Fintype.equivFin {v : Fin m // q v = u.1}).symm u.2).property
  let iso : graph G₀ copies ≃g H := {
    toEquiv := label
    map_rel_iff' := by
      intro u v
      change H.Adj (label u) (label v) ↔ G₀.Adj u.1 v.1
      rw [hAdj₀, hlabel, hlabel] }
  have hcount : (graph G₀ copies).edgeSet.ncard = H.edgeSet.ncard := by
    have h := Fintype.card_congr iso.mapEdgeSet
    simpa only [Set.fintypeCard_eq_ncard] using h
  let M : ℝ := (H.edgeSet.ncard : ℝ) + 1
  have hM : 1 ≤ M := by dsimp [M]; exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hpow : 1 ≤ Real.rpow M b := Real.one_le_rpow hM hb
  obtain ⟨D₀, hD₀⟩ := hbase r G₀ hG₀
  have hbags (j : D₀.Node) : ((D₀.bag j).card : ℝ) ≤ c * Real.rpow M b := by
    exact (hD₀ j).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (by dsimp [M]; exact_mod_cast Nat.add_le_add_right hedge 1) hb) hc.le)
  let w := Nat.ceil ((c + 1) * Real.rpow M b) - 1
  have hceilpos : 1 ≤ Nat.ceil ((c + 1) * Real.rpow M b) := Nat.one_le_ceil_iff.mpr (by positivity)
  have hw : w + 1 = Nat.ceil ((c + 1) * Real.rpow M b) := Nat.sub_add_cancel hceilpos
  have hwidth : HasTreewidthAtMost G₀ w := by
    refine ⟨D₀, fun j => ?_⟩
    rw [hw]
    have hcard : ((D₀.bag j).card : ℝ) ≤ (Nat.ceil ((c + 1) * Real.rpow M b) : ℝ) :=
      (hbags j).trans ((by nlinarith : c * Real.rpow M b ≤ (c + 1) * Real.rpow M b).trans (Nat.le_ceil _))
    exact_mod_cast hcard
  have hwidth_bound : (w + 1 : ℕ) ≤ (c + 2) * Real.rpow ((graph G₀ copies).edgeSet.ncard + 1) b := by
    rw [hw, hcount]
    have h := (Nat.ceil_lt_add_one (show 0 ≤ (c + 1) * Real.rpow M b by positivity)).le
    change (Nat.ceil ((c + 1) * Real.rpow M b) : ℝ) ≤ (c + 2) * Real.rpow M b
    nlinarith
  obtain ⟨D, hD⟩ := Lax263307.BlowUpDeletion.power_bound G₀ copies w b (c + 2) hb hb1 (by linarith)
    hwidth hwidth_bound
  let E := Lax263307Proofs.TreeExtensions.pullback iso.symm.toRelEmbedding D
  refine ⟨E, fun j => ?_⟩
  have hcard : ((E.bag j).card : ℝ) ≤ ((D.bag j).card : ℝ) := by
    exact_mod_cast Lax263307Proofs.TreeExtensions.pullback_card iso.symm.toRelEmbedding D j
  exact hcard.trans (by simpa only [hcount] using hD j)


/--
---
conclusion: Lax263307.BlowUpBagBounds.blowup_power_bag_bound
---
Raise the real sublinear blow-up bag bound to a fixed positive integer
power, absorb its constant into a positive integer, and dominate its
exponent by a-1 using a(1-beta)>1.
-/
theorem blowup_power_bag_bound (C : GraphClass) (hereditary : IsHereditary C)
    (separators : HasStronglyEdgeSublinearSeparators C) :
    ∃ a A : ℕ, 0 < a ∧ 0 < A ∧ Lax263307.PowerBagBounds.HasPowerBagBound (blowUpClass C) a A := by
  obtain ⟨β, c, _hβ, hβ1, hc, hbags⟩ := Lax263307.BlowUpBagBounds.blowup_sublinear_bag_bound C hereditary separators
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


end Lax263307Proofs.BlowUpBagBounds
