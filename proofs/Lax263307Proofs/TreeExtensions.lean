import Lax263307.BlowUpDecompositions
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

namespace Lax263307Proofs.TreeExtensions

open Lax228581.Treewidth

/-- Attach a new leaf for every element of `β` at the chosen root. -/
def attachLeaves {α β : Type} (T : SimpleGraph α) (root : α) :
    SimpleGraph (α ⊕ β) where
  Adj
    | .inl a, .inl b => T.Adj a b
    | .inl a, .inr _ => a = root
    | .inr _, .inl b => b = root
    | .inr _, .inr _ => False
  symm := ⟨by intro a b h; cases a <;> cases b <;> simp_all [T.adj_comm]⟩
  loopless := ⟨by intro a; cases a <;> simp⟩

theorem degree_as_sum {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) :
    G.degree v = ∑ u, if G.Adj v u then 1 else 0 := by
  classical
  rw [SimpleGraph.degree, G.neighborFinset_eq_filter]
  simp

theorem attachLeaves_tree {α β : Type} [Fintype α] [Fintype β]
    (T : SimpleGraph α) (root : α) (hT : T.IsTree) :
    (attachLeaves (β := β) T root).IsTree := by
  classical
  let H := attachLeaves (β := β) T root
  let inclusion : T →g H := ⟨Sum.inl, fun h => h⟩
  have hroot : ∀ a : α ⊕ β, H.Reachable a (.inl root) := by
    intro a
    cases a with
    | inl a => exact (hT.connected a root).map inclusion
    | inr b => exact SimpleGraph.Adj.reachable (show H.Adj (.inr b) (.inl root) from rfl)
  have : Nonempty (α ⊕ β) := ⟨.inl root⟩
  have hconn : H.Connected := ⟨fun a b => (hroot a).trans (hroot b).symm⟩
  have hleft (a : α) : H.degree (.inl a) =
      T.degree a + if a = root then Fintype.card β else 0 := by
    rw [degree_as_sum, Fintype.sum_sum_type, degree_as_sum]
    simp only [H, attachLeaves]
    split_ifs <;> simp_all
  have hright (b : β) : H.degree (.inr b) = 1 := by
    rw [degree_as_sum, Fintype.sum_sum_type]
    simp [H, attachLeaves, eq_comm]
  have hsum : (∑ v, H.degree v) = (∑ a, T.degree a) + 2 * Fintype.card β := by
    rw [Fintype.sum_sum_type]
    simp_rw [hleft, hright]
    simp [Finset.sum_add_distrib]
    omega
  change H.IsTree
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨hconn, ?_⟩
  have hcount := hT.card_edgeFinset
  have hhand := H.sum_degrees_eq_twice_card_edges
  rw [hsum, T.sum_degrees_eq_twice_card_edges] at hhand
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_sum,
    ← SimpleGraph.edgeFinset_card]
  omega

/-- Old bags keep their vertices; each formerly omitted isolated vertex gets
its own singleton bag. -/
noncomputable def isolatedBag {V : Type} [DecidableEq V] {G : SimpleGraph V} (S : Set V)
    (D : TreeDecomposition (G.induce S)) : D.Node ⊕ ↥(Sᶜ) → Finset V
  | .inl i => (D.bag i).image Subtype.val
  | .inr v => {v.val}

theorem isolatedBag_connected {V : Type} [DecidableEq V] {G : SimpleGraph V} (S : Set V)
    (D : TreeDecomposition (G.induce S)) (root : D.Node) (v : V) :
    ((attachLeaves (β := ↥(Sᶜ)) D.tree root).induce
      {i | v ∈ isolatedBag S D i}).Connected := by
  classical
  by_cases hv : v ∈ S
  · let old := D.tree.induce {i | (⟨v, hv⟩ : S) ∈ D.bag i}
    let new := (attachLeaves (β := ↥(Sᶜ)) D.tree root).induce
      {i | v ∈ isolatedBag S D i}
    let f : old →g new :=
      { toFun := fun i => ⟨.inl i.val, by
          change v ∈ (D.bag i.val).image Subtype.val
          exact Finset.mem_image.mpr ⟨⟨v, hv⟩, i.property, rfl⟩⟩
        map_rel' := fun h => h }
    apply (D.bag_indices_connected ⟨v, hv⟩).map f
    rintro ⟨i, hi⟩
    cases i with
    | inl i =>
      have hi' : (⟨v, hv⟩ : S) ∈ D.bag i := by
        obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hi
        have : u = ⟨v, hv⟩ := Subtype.ext he
        simpa [this] using hu
      exact ⟨⟨i, hi'⟩, rfl⟩
    | inr u =>
      have : v = u.val := by simpa [isolatedBag] using hi
      exact (u.property (this ▸ hv)).elim
  · let new := (attachLeaves (β := ↥(Sᶜ)) D.tree root).induce
      {i | v ∈ isolatedBag S D i}
    let newV := {i : D.Node ⊕ ↥(Sᶜ) // v ∈ isolatedBag S D i}
    have hi : ∀ i : newV, i.val = .inr ⟨v, hv⟩ := by
      rintro ⟨i, hi⟩
      cases i with
      | inl i =>
        obtain ⟨u, _, he⟩ := Finset.mem_image.mp hi
        exact (hv (he ▸ u.property)).elim
      | inr u =>
        have : v = u.val := by simpa [isolatedBag] using hi
        exact congrArg Sum.inr (Subtype.ext this.symm)
    have : Subsingleton newV := ⟨fun a b => Subtype.ext ((hi a).trans (hi b).symm)⟩
    have : Nonempty newV := ⟨⟨.inr ⟨v, hv⟩, by simp [isolatedBag]⟩⟩
    change new.Connected
    exact
      { preconnected := fun a b => by
          have he : a = b := ‹Subsingleton newV›.elim a b
          subst b
          exact SimpleGraph.Reachable.refl _
        nonempty := ‹Nonempty newV› }

/-- Insert the omitted isolated vertices without increasing any old bag. -/
noncomputable def extendIsolated {V : Type} [Fintype V] {G : SimpleGraph V}
    (S : Set V) (isolated : ∀ v, v ∉ S → G.IsIsolated v)
    (D : TreeDecomposition (G.induce S)) : TreeDecomposition G := by
  classical
  letI := D.nodeFintype
  have : Nonempty D.Node := D.isTree.connected.nonempty
  let root := Classical.arbitrary D.Node
  exact
    { Node := D.Node ⊕ ↥(Sᶜ)
      tree := attachLeaves D.tree root
      isTree := attachLeaves_tree D.tree root D.isTree
      bag := isolatedBag S D
      vertex_mem_bag := by
        intro v
        by_cases hv : v ∈ S
        · obtain ⟨i, hi⟩ := D.vertex_mem_bag ⟨v, hv⟩
          exact ⟨.inl i, Finset.mem_image.mpr ⟨⟨v, hv⟩, hi, rfl⟩⟩
        · exact ⟨.inr ⟨v, hv⟩, by simp [isolatedBag]⟩
      edge_mem_bag := by
        intro u v huv
        have hu : u ∈ S := by
          by_contra hu
          exact isolated u hu v huv
        have hv : v ∈ S := by
          by_contra hv
          exact isolated v hv u huv.symm
        obtain ⟨i, hiu, hiv⟩ := D.edge_mem_bag
          (show (G.induce S).Adj ⟨u, hu⟩ ⟨v, hv⟩ from huv)
        exact ⟨.inl i, Finset.mem_image.mpr ⟨⟨u, hu⟩, hiu, rfl⟩,
          Finset.mem_image.mpr ⟨⟨v, hv⟩, hiv, rfl⟩⟩
      bag_indices_connected := isolatedBag_connected S D root }

theorem extendIsolated_card {V : Type} [Fintype V] {G : SimpleGraph V}
    (S : Set V) (isolated : ∀ v, v ∉ S → G.IsIsolated v)
    (D : TreeDecomposition (G.induce S)) (B : ℕ) (hB : 1 ≤ B)
    (hD : ∀ i, (D.bag i).card ≤ B) :
    ∀ i, ((extendIsolated S isolated D).bag i).card ≤ B := by
  classical
  intro i
  cases i with
  | inl i => exact Finset.card_image_le.trans (hD i)
  | inr v => simpa [extendIsolated, isolatedBag] using hB

/-- Pull a decomposition back along an induced embedding. -/
noncomputable def pullback {V W : Type} [Fintype V] {G : SimpleGraph V}
    {H : SimpleGraph W} (f : G ↪g H) (D : TreeDecomposition H) :
    TreeDecomposition G := by
  classical
  exact
    { Node := D.Node
      nodeFintype := D.nodeFintype
      tree := D.tree
      isTree := D.isTree
      bag := fun i => Finset.univ.filter fun v => f v ∈ D.bag i
      vertex_mem_bag := by
        intro v
        obtain ⟨i, hi⟩ := D.vertex_mem_bag (f v)
        exact ⟨i, by simp [hi]⟩
      edge_mem_bag := by
        intro u v huv
        obtain ⟨i, hiu, hiv⟩ := D.edge_mem_bag (f.map_adj_iff.mpr huv)
        exact ⟨i, by simp [hiu], by simp [hiv]⟩
      bag_indices_connected := by
        intro v
        have hset : {i | v ∈ Finset.univ.filter fun v => f v ∈ D.bag i} =
            {i | f v ∈ D.bag i} := by ext i; simp
        rw [hset]
        exact D.bag_indices_connected (f v) }

theorem pullback_card {V W : Type} [Fintype V] {G : SimpleGraph V}
    {H : SimpleGraph W} (f : G ↪g H) (D : TreeDecomposition H) (i : D.Node) :
    ((pullback f D).bag i).card ≤ (D.bag i).card := by
  classical
  let B := (pullback f D).bag i
  calc
    B.card = (B.image f).card := (Finset.card_image_of_injective B f.injective).symm
    _ ≤ (D.bag i).card := Finset.card_le_card (by
      intro w hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      exact (Finset.mem_filter.mp hv).2)

/-- Restore a deleted set by adding it to every bag. -/
noncomputable def restoreDeleted {V : Type} [Fintype V] {G : SimpleGraph V}
    (X : Finset V) (D : TreeDecomposition (G.induce (↑X : Set V)ᶜ)) :
    TreeDecomposition G := by
  classical
  have : Nonempty D.Node := D.isTree.connected.nonempty
  exact
    { Node := D.Node
      nodeFintype := D.nodeFintype
      tree := D.tree
      isTree := D.isTree
      bag := fun i => X ∪ (D.bag i).image Subtype.val
      vertex_mem_bag := by
        intro v
        by_cases hv : v ∈ X
        · exact ⟨Classical.arbitrary D.Node, by simp [hv]⟩
        · obtain ⟨i, hi⟩ := D.vertex_mem_bag ⟨v, hv⟩
          exact ⟨i, Finset.mem_union_right X (Finset.mem_image.mpr ⟨⟨v, hv⟩, hi, rfl⟩)⟩
      edge_mem_bag := by
        intro u v huv
        by_cases hu : u ∈ X <;> by_cases hv : v ∈ X
        · exact ⟨Classical.arbitrary D.Node, by simp [hu, hv]⟩
        · obtain ⟨i, hi⟩ := D.vertex_mem_bag ⟨v, hv⟩
          exact ⟨i, by simp [hu], Finset.mem_union_right X
            (Finset.mem_image.mpr ⟨⟨v, hv⟩, hi, rfl⟩)⟩
        · obtain ⟨i, hi⟩ := D.vertex_mem_bag ⟨u, hu⟩
          exact ⟨i, Finset.mem_union_right X
            (Finset.mem_image.mpr ⟨⟨u, hu⟩, hi, rfl⟩), by simp [hv]⟩
        · obtain ⟨i, hiu, hiv⟩ := D.edge_mem_bag
            (show (G.induce (↑X : Set V)ᶜ).Adj ⟨u, hu⟩ ⟨v, hv⟩ from huv)
          exact ⟨i, Finset.mem_union_right X
            (Finset.mem_image.mpr ⟨⟨u, hu⟩, hiu, rfl⟩), Finset.mem_union_right X
            (Finset.mem_image.mpr ⟨⟨v, hv⟩, hiv, rfl⟩)⟩
      bag_indices_connected := by
        intro v
        by_cases hv : v ∈ X
        · have hset : {i | v ∈ X ∪ (D.bag i).image Subtype.val} = Set.univ := by
            ext i; simp [hv]
          rw [hset]
          exact (SimpleGraph.induceUnivIso D.tree).connected_iff.mpr D.isTree.connected
        · have hset : {i | v ∈ X ∪ (D.bag i).image Subtype.val} =
              {i | (⟨v, hv⟩ : ↥((↑X : Set V)ᶜ)) ∈ D.bag i} := by
            ext i
            simp only [Finset.mem_union, hv, false_or, Finset.mem_image]
            constructor
            · rintro ⟨u, hu, he⟩
              have : u = ⟨v, hv⟩ := Subtype.ext he
              simpa [this] using hu
            · intro hi
              exact ⟨⟨v, hv⟩, hi, rfl⟩
          rw [hset]
          exact D.bag_indices_connected ⟨v, hv⟩ }

theorem restoreDeleted_card {V : Type} [Fintype V] {G : SimpleGraph V}
    (X : Finset V) (D : TreeDecomposition (G.induce (↑X : Set V)ᶜ)) (B : ℕ)
    (hD : ∀ i, (D.bag i).card ≤ B) :
    ∀ i, ((restoreDeleted X D).bag i).card ≤ X.card + B := by
  classical
  intro i
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add_left (Finset.card_image_le.trans (hD i)) X.card)

end Lax263307Proofs.TreeExtensions
