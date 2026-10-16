import Lax263307Proofs.TreeExtensions
import Lax263307.SeparatorDecompositions
import Lax263307Proofs.SeparatorComponents
import Mathlib.Tactic

namespace Lax263307Proofs.SeparatorDecompositions

variable {ι : Type} {V : ι → Type}

def join (T : ∀ i, SimpleGraph (V i)) (root : ∀ i, V i) : SimpleGraph (Unit ⊕ Sigma V) where
  Adj
    | .inl _, .inl _ => False
    | .inl _, .inr ⟨i, v⟩ => v = root i
    | .inr ⟨i, v⟩, .inl _ => v = root i
    | .inr ⟨i, u⟩, .inr ⟨j, v⟩ => ∃ h : i = j, (T i).Adj u (h.symm ▸ v)
  symm := ⟨by
    intro a b hab
    cases a with
    | inl a => cases b <;> exact hab
    | inr a =>
      cases b with
      | inl b => exact hab
      | inr b =>
        rcases a with ⟨i, u⟩
        rcases b with ⟨j, v⟩
        obtain ⟨h, hadj⟩ := hab
        subst j
        exact ⟨rfl, hadj.symm⟩⟩
  loopless := ⟨by
    intro a
    cases a with
    | inl a => exact id
    | inr a =>
      rcases a with ⟨i, v⟩
      rintro ⟨h, hadj⟩
      exact (T i).ne_of_adj hadj rfl⟩

noncomputable instance (T : ∀ i, SimpleGraph (V i)) (root : ∀ i, V i) : DecidableRel (join T root).Adj :=
  fun _ _ => Classical.propDecidable _

variable [Fintype ι] [∀ i, Fintype (V i)]

theorem join_tree (T : ∀ i, SimpleGraph (V i)) (root : ∀ i, V i) (trees : ∀ i, (T i).IsTree) :
    (join T root).IsTree := by
  classical
  let H := join T root
  have hreach : ∀ a : Unit ⊕ Sigma V, H.Reachable a (.inl ()) := by
    intro a
    cases a with
    | inl a => cases a; exact SimpleGraph.Reachable.refl _
    | inr a =>
      rcases a with ⟨i, u⟩
      let inclusion : T i →g H := {
        toFun := fun v => .inr ⟨i, v⟩
        map_rel' := fun h => ⟨rfl, h⟩ }
      exact ((trees i).connected u (root i)).map inclusion |>.trans
        (SimpleGraph.Adj.reachable (show H.Adj (.inr ⟨i, root i⟩) (.inl ()) from rfl))
  have hconnected : H.Connected := {
    preconnected := fun a b => (hreach a).trans (hreach b).symm
    nonempty := ⟨.inl ()⟩ }
  have hrootdegree : H.degree (.inl ()) = Fintype.card ι := by
    rw [Lax263307Proofs.TreeExtensions.degree_as_sum, Fintype.sum_sum_type, Fintype.sum_sigma]
    simp [H, join]
  have hchilddegree (i : ι) (u : V i) :
      H.degree (.inr ⟨i, u⟩) = (T i).degree u + (if u = root i then 1 else 0) := by
    rw [Lax263307Proofs.TreeExtensions.degree_as_sum, Fintype.sum_sum_type, Fintype.sum_sigma]
    have hinner (j : ι) : (∑ v : V j, if H.Adj (.inr ⟨i, u⟩) (.inr ⟨j, v⟩) then 1 else 0) =
        if j = i then (T i).degree u else 0 := by
      by_cases h : j = i
      · subst j
        simpa [H, join] using (Lax263307Proofs.TreeExtensions.degree_as_sum (T i) u).symm
      · have hne : i ≠ j := Ne.symm h
        simp [H, join, h, hne]
    simp_rw [hinner]
    simp [H, join, add_comm]
  have heach (i : ι) : (∑ v : V i, (T i).degree v) + 2 = 2 * Fintype.card (V i) := by
    have htree := (trees i).card_edgeFinset
    have hhand := (T i).sum_degrees_eq_twice_card_edges
    omega
  have hsums : (∑ i, ∑ v : V i, (T i).degree v) + 2 * Fintype.card ι =
      2 * ∑ i, Fintype.card (V i) := by
    have h := Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset ι)) => heach i)
    simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Finset.mul_sum, Nat.mul_comm] using h
  have hsum : (∑ v, H.degree v) = 2 * ∑ i, Fintype.card (V i) := by
    rw [Fintype.sum_sum_type, Fintype.sum_sigma]
    simp_rw [hchilddegree, Finset.sum_add_distrib]
    simp [hrootdegree]
    omega
  change H.IsTree
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨hconnected, ?_⟩
  have hhand := H.sum_degrees_eq_twice_card_edges
  rw [hsum] at hhand
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_sigma,
    ← SimpleGraph.edgeFinset_card]
  simp only [Fintype.card_unit]
  omega

open Lax228581.Treewidth Lax263307.SeparatorComponents
open Lax263307Proofs.SeparatorComponents (components)
open Lax263307.GraphClasses Lax263307.EdgeSublinearSeparators

variable {n : ℕ} {G : SimpleGraph (Fin n)} {S : Finset (Fin n)}

noncomputable def bag (P : Partition G S ι)
    (D : ∀ i, TreeDecomposition (G.induce (↑(P.vertices i) : Set (Fin n)))) :
    Unit ⊕ (Σ i, (D i).Node) → Finset (Fin n)
  | .inl _ => S
  | .inr ⟨i, j⟩ => S ∪ ((D i).bag j).image Subtype.val

theorem bag_connected (P : Partition G S ι)
    (D : ∀ i, TreeDecomposition (G.induce (↑(P.vertices i) : Set (Fin n))))
    (root : ∀ i, (D i).Node) (v : Fin n) :
    ((join (fun i => (D i).tree) root).induce {j | v ∈ bag P D j}).Connected := by
  classical
  let T := join (fun i => (D i).tree) root
  let H := T.induce {j | v ∈ bag P D j}
  by_cases hv : v ∈ S
  · have hall (j : Unit ⊕ (Σ i, (D i).Node)) : v ∈ bag P D j := by
      cases j <;> simp [bag, hv]
    let : ∀ i, Fintype (D i).Node := fun i => (D i).nodeFintype
    let f : T →g H := { toFun := fun j => ⟨j, hall j⟩, map_rel' := fun h => h }
    exact (join_tree (fun i => (D i).tree) root (fun i => (D i).isTree)).connected.map f
      (fun ⟨j, _⟩ => ⟨j, rfl⟩)
  · obtain ⟨i, hi, hunique⟩ := P.unique v hv
    let u : ↥(↑(P.vertices i) : Set (Fin n)) := ⟨v, hi⟩
    let K := (D i).tree.induce {j | u ∈ (D i).bag j}
    let f : K →g H := {
      toFun := fun j => ⟨.inr ⟨i, j.val⟩, Finset.mem_union_right S
        (Finset.mem_image.mpr ⟨u, j.property, rfl⟩)⟩
      map_rel' := fun h => ⟨rfl, h⟩ }
    apply ((D i).bag_indices_connected u).map f
    rintro ⟨j, hj⟩
    cases j with
    | inl j => exact (hv hj).elim
    | inr j =>
      rcases j with ⟨k, j⟩
      obtain ⟨w, hw, he⟩ := Finset.mem_image.mp ((Finset.mem_union.mp hj).resolve_left hv)
      have hk : k = i := hunique k (he ▸ w.property)
      subst k
      have hwu : w = u := Subtype.ext he
      exact ⟨⟨j, by simpa [hwu] using hw⟩, rfl⟩

noncomputable def glue (P : Partition G S ι)
    (D : ∀ i, TreeDecomposition (G.induce (↑(P.vertices i) : Set (Fin n)))) :
    TreeDecomposition G := by
  classical
  let : ∀ i, Fintype (D i).Node := fun i => (D i).nodeFintype
  let root (i : ι) : (D i).Node := Classical.choice (D i).isTree.connected.nonempty
  exact {
    Node := Unit ⊕ (Σ i, (D i).Node)
    tree := join (fun i => (D i).tree) root
    isTree := join_tree (fun i => (D i).tree) root (fun i => (D i).isTree)
    bag := bag P D
    vertex_mem_bag := by
      intro v
      by_cases hv : v ∈ S
      · exact ⟨.inl (), hv⟩
      · obtain ⟨i, hi, _⟩ := P.unique v hv
        obtain ⟨j, hj⟩ := (D i).vertex_mem_bag ⟨v, hi⟩
        exact ⟨.inr ⟨i, j⟩, Finset.mem_union_right S
          (Finset.mem_image.mpr ⟨⟨v, hi⟩, hj, rfl⟩)⟩
    edge_mem_bag := by
      intro u v huv
      by_cases hu : u ∈ S
      · by_cases hv : v ∈ S
        · exact ⟨.inl (), hu, hv⟩
        · obtain ⟨i, hi, _⟩ := P.unique v hv
          obtain ⟨j, hj⟩ := (D i).vertex_mem_bag ⟨v, hi⟩
          exact ⟨.inr ⟨i, j⟩, Finset.mem_union_left _ hu,
            Finset.mem_union_right S (Finset.mem_image.mpr ⟨⟨v, hi⟩, hj, rfl⟩)⟩
      · obtain ⟨i, hi, _⟩ := P.unique u hu
        by_cases hv : v ∈ S
        · obtain ⟨j, hj⟩ := (D i).vertex_mem_bag ⟨u, hi⟩
          exact ⟨.inr ⟨i, j⟩, Finset.mem_union_right S
            (Finset.mem_image.mpr ⟨⟨u, hi⟩, hj, rfl⟩), Finset.mem_union_left _ hv⟩
        · have hvpart := P.closed i u v hi hv huv
          obtain ⟨j, hju, hjv⟩ := (D i).edge_mem_bag
            (show (G.induce (↑(P.vertices i) : Set (Fin n))).Adj ⟨u, hi⟩ ⟨v, hvpart⟩ from huv)
          exact ⟨.inr ⟨i, j⟩,
            Finset.mem_union_right S (Finset.mem_image.mpr ⟨⟨u, hi⟩, hju, rfl⟩),
            Finset.mem_union_right S (Finset.mem_image.mpr ⟨⟨v, hvpart⟩, hjv, rfl⟩)⟩
    bag_indices_connected := bag_connected P D root }

theorem glue_card (P : Partition G S ι)
    (D : ∀ i, TreeDecomposition (G.induce (↑(P.vertices i) : Set (Fin n))))
    (B : ℕ) (bound : ∀ i j, ((D i).bag j).card ≤ B) :
    ∀ j, ((glue P D).bag j).card ≤ S.card + B := by
  classical
  intro j
  cases j with
  | inl j => change S.card ≤ S.card + B; omega
  | inr j =>
    rcases j with ⟨i, j⟩
    exact (Finset.card_union_le S (((D i).bag j).image Subtype.val)).trans (Nat.add_le_add_left
      (Finset.card_image_le.trans (bound i j)) S.card)


/--
---
conclusion: Lax263307.SeparatorDecompositions.glue_bound
---
Join the child trees at a new separator root. Vertices of the separator
occur throughout the tree; each other vertex has exactly its original
connected set of child bags. Closure of the partition covers every edge.
-/
theorem glue_bound {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    {ι : Type} [Fintype ι] (P : Partition G S ι)
    (D : ∀ i, TreeDecomposition (G.induce (↑(P.vertices i) : Set (Fin n))))
    (B : ℕ) (bound : ∀ i j, ((D i).bag j).card ≤ B) :
    ∃ E : TreeDecomposition G, ∀ j, (E.bag j).card ≤ S.card + B :=
  ⟨glue P D, glue_card P D B bound⟩


noncomputable def oneBag {V : Type} [Fintype V] (G : SimpleGraph V) : TreeDecomposition G := by
  classical
  exact {
    Node := Unit
    tree := ⊥
    isTree := SimpleGraph.IsTree.of_subsingleton
    bag := fun _ => Finset.univ
    vertex_mem_bag := fun v => ⟨(), Finset.mem_univ v⟩
    edge_mem_bag := fun {_ _} _ => ⟨(), Finset.mem_univ _, Finset.mem_univ _⟩
    bag_indices_connected := fun v => by
      have : Nonempty {i : Unit // v ∈ (Finset.univ : Finset V)} := ⟨⟨(), Finset.mem_univ v⟩⟩
      exact { preconnected := SimpleGraph.Preconnected.of_subsingleton, nonempty := this } }

theorem embedding_edge_bound {V W : Type} [Fintype V] [Fintype W]
    {H : SimpleGraph V} {G : SimpleGraph W} (f : H ↪g G) : H.edgeSet.ncard ≤ G.edgeSet.ncard := by
  classical
  have h := Fintype.card_le_of_injective f.mapEdgeSet f.mapEdgeSet.injective
  simpa only [Set.fintypeCard_eq_ncard] using h

theorem components_balanced {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (balanced : IsBalancedSeparator G S) :
    ∀ i, 3 * ((components G S).vertices i).card ≤ 2 * n := by
  classical
  intro i
  have hcard : ((components G S).vertices i).card = i.supp.ncard := by
    change (Subtype.val '' i.supp).toFinset.card = _
    rw [Set.toFinset_card, Set.fintypeCard_eq_ncard, Set.ncard_image_of_injective i.supp Subtype.val_injective]
  rw [hcard]
  exact balanced i

/--
---
conclusion: Lax263307.SeparatorDecompositions.recursive_bag_bound
---
Induct on the graph order. Relabel each component by a finite numbered
vertex set, apply heredity and the induction hypothesis, and pull its
decomposition back. Its edge count cannot increase, and balance consumes
one depth level. Joining the children adds just the separator bound.
-/
theorem recursive_bag_bound (C : GraphClass) (hereditary : IsHereditary C)
    (B : ℕ → ℕ) (monotone : Monotone B) (positive : ∀ m, 1 ≤ B m)
    (separators : ∀ n (G : SimpleGraph (Fin n)), G ∈ C n →
      ∃ S : Finset (Fin n), IsBalancedSeparator G S ∧ S.card ≤ B G.edgeSet.ncard)
    {n : ℕ} (G : SimpleGraph (Fin n)) (member : G ∈ C n) :
    ∃ D : TreeDecomposition G, ∀ j,
      (D.bag j).card ≤ B G.edgeSet.ncard * (Lax263307.RecursionDepth.depth n + 1) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n ≤ 1
    · refine ⟨oneBag G, ?_⟩
      intro j
      change (Finset.univ : Finset (Fin n)).card ≤ _
      simp only [Finset.card_univ, Fintype.card_fin]
      rw [Lax263307.RecursionDepth.depth, if_pos hn]
      simpa using hn.trans (positive G.edgeSet.ncard)
    · obtain ⟨S, hbalanced, hS⟩ := separators n G member
      let P := components G S
      let I := (G.induce (↑S : Set (Fin n))ᶜ).ConnectedComponent
      let : Fintype I := Fintype.ofFinite I
      have hpart := components_balanced G S hbalanced
      have child (i : I) : ∃ D : TreeDecomposition (G.induce (↑(P.vertices i) : Set (Fin n))),
          ∀ j, (D.bag j).card ≤ B G.edgeSet.ncard * Lax263307.RecursionDepth.depth n := by
        let U := ↥(↑(P.vertices i) : Set (Fin n))
        let r := Fintype.card U
        let e : U ≃ Fin r := Fintype.equivFin U
        let H := (G.induce (↑(P.vertices i) : Set (Fin n))).comap e.symm
        let f : H ↪g G := {
          toFun := fun v => (e.symm v).val
          inj' := fun a b h => e.symm.injective (Subtype.ext h)
          map_rel_iff' := Iff.rfl }
        have hr : r = (P.vertices i).card := Fintype.card_coe _
        have hrbal : 3 * r ≤ 2 * n := by rw [hr]; exact hpart i
        have hH := hereditary r n H G member ⟨f⟩
        obtain ⟨D, hD⟩ := ih r (by omega) H hH
        let g : (G.induce (↑(P.vertices i) : Set (Fin n))) ↪g H := {
          toFun := e
          inj' := e.injective
          map_rel_iff' := by intro a b; simp [H] }
        let E := Lax263307Proofs.TreeExtensions.pullback g D
        refine ⟨E, fun j => ?_⟩
        have hm := monotone (embedding_edge_bound f)
        have hd := Lax263307.RecursionDepth.balanced_decrease n r (by omega) hrbal
        exact (Lax263307Proofs.TreeExtensions.pullback_card g D j).trans
          ((hD j).trans (Nat.mul_le_mul hm hd))
      choose D hD using child
      obtain ⟨E, hE⟩ := Lax263307.SeparatorDecompositions.glue_bound G S P D
        (B G.edgeSet.ncard * Lax263307.RecursionDepth.depth n) hD
      refine ⟨E, fun j => (hE j).trans ?_⟩
      nlinarith

end Lax263307Proofs.SeparatorDecompositions
