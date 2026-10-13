import Lax263307.ComputedSeparators
import Lax263307Proofs.LightSeparators
import Lax263307Proofs.CutTraces
import Mathlib.Tactic

namespace Lax263307Proofs.ComputedSeparators

open scoped NNReal NNRat
open Lax263307.ComputedSeparators Lax263307.GraphClasses Lax263307.PowerBagBounds
open Lax263307.VertexSplitting Lax263307.Entropy Lax263307.RepeatedCutAccounting
open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax455465.ConcurrentFlow
open Lax263307Proofs.LightSeparators

theorem decode_cut_certificate {n : ℕ} (c : Lax455465.FlowCutCertificate.Certificate n) :
    decodeCut n (Lax455465.FlowCutCertificate.encodeCertificate c) = c.cut := by
  ext v
  unfold decodeCut
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  change (encodeCut c.cut ++ encodeArcs c.flow).getD v.val 0 = 1 ↔ v ∈ c.cut
  have hv : v.val < (encodeCut c.cut).length := by simp [encodeCut]
  rw [List.getD_append _ _ 0 v.val hv, List.getD_eq_getElem _ 0 hv]
  simp [encodeCut]

def embedding {n : ℕ} (G : SimpleGraph (Fin n)) (R : Finset (Fin n)) : restriction G R ↪g G where
  toFun := label R
  inj' := (label R).injective
  map_rel_iff' := Iff.rfl

theorem oriented {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → ℝ) (ρ γ : ℝ)
    (A B : Finset (Fin n)) (ha : A.Nonempty) (hb : B.Nonempty)
    (cover : A ∪ B = Finset.univ)
    (separated : ∀ u ∈ A \ B, ∀ v ∈ B \ A, ¬G.Adj u v)
    (bound : cost x (A ∩ B) ≤ 4 * ρ * A.card * B.card / γ) :
    let s := Lax263307.ComputedSeparators.orient A B
    s.1 ∪ s.2 = Finset.univ ∧ s.2.Nonempty ∧ 2 * (s.2 \ s.1).card ≤ n ∧
      (∀ u ∈ s.1 \ s.2, ∀ v ∈ s.2 \ s.1, ¬G.Adj u v) ∧
      cost x (s.1 ∩ s.2) ≤ 4 * ρ * s.1.card * s.2.card / γ := by
  dsimp only [Lax263307.ComputedSeparators.orient]
  split_ifs with h
  · exact ⟨cover, hb, small_piece A B cover h, separated, bound⟩
  · refine ⟨by rw [Finset.union_comm]; exact cover, ha,
      small_piece B A (by rw [Finset.union_comm]; exact cover) (by omega), ?_, ?_⟩
    · intro u hu v hv hadj
      exact separated v hv u hu hadj.symm
    · rw [Finset.inter_comm]
      convert bound using 1
      ring

theorem lifted {r n : ℕ} (H : SimpleGraph (Fin r)) (G : SimpleGraph (Fin n))
    (f : H ↪g G) (R : Finset (Fin n)) (onto : Finset.univ.image f = R)
    (x : Fin n → ℝ) (ρ γ : ℝ) (A B : Finset (Fin r))
    (cover : A ∪ B = Finset.univ) (nonempty : B.Nonempty)
    (small : 2 * (B \ A).card ≤ r)
    (separated : ∀ u ∈ A \ B, ∀ v ∈ B \ A, ¬H.Adj u v)
    (bound : cost (x ∘ f) (A ∩ B) ≤ 4 * ρ * A.card * B.card / γ) :
    A.image f ∪ B.image f = R ∧ (B.image f).Nonempty ∧
      2 * (B.image f \ A.image f).card ≤ R.card ∧
      (∀ u ∈ A.image f \ B.image f, ∀ v ∈ B.image f \ A.image f, ¬G.Adj u v) ∧
      cost x (A.image f ∩ B.image f) ≤ 4 * ρ * (A.image f).card * (B.image f).card / γ := by
  have hcard (S : Finset (Fin r)) : (S.image f).card = S.card :=
    Finset.card_image_of_injective _ f.injective
  have hR : R.card = r := by rw [← onto, hcard, Finset.card_univ, Fintype.card_fin]
  refine ⟨?_, nonempty.image f, ?_, ?_, ?_⟩
  · rw [← Finset.image_union, cover, onto]
  · rw [← Finset.image_sdiff B A f.injective, hcard, hR]
    exact small
  · intro u hu v hv hadj
    rw [← Finset.image_sdiff A B f.injective] at hu
    rw [← Finset.image_sdiff B A f.injective] at hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
    exact separated a ha b hb (f.map_adj_iff.mp hadj)
  · rw [← Finset.image_inter A B f.injective, hcard, hcard]
    unfold cost
    rw [Finset.sum_image (fun _ _ _ _ h => f.injective h)]
    exact bound

theorem exists_solver (C : GraphClass) (hereditary : IsHereditary C)
    (a A : ℕ) (ha : 0 < a) (hA : 0 < A) (class_bound : HasPowerBagBound C a A) :
    ∃ (solve : List ℕ → List ℕ) (K B : ℕ), Lax759944.RamPolytime.RamPolytime solve ∧
      0 < K ∧ 0 < B ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G ∈ C n → 0 < n → ∀ (x : Fin n → ℚ≥0) (k p ℓ : ℕ),
      0 < k → 0 < p → 0 < ℓ →
      (∀ v, (x v : ℝ) ≤ 1) → (∑ v, (x v : ℝ)) ≤ k →
      edgeCost G (fun v => (x v : ℝ)) ≤ (k : ℝ) ^ 2 / p →
      (K : ℝ) * ((ℓ : ℝ) + 1) ^ (4 * a + 2) ≤ k →
      (2 * K : ℝ) * ((ℓ : ℝ) + 1) ^ (4 * a + 2) ≤ p →
      ∀ R : Finset (Fin n), 2 * n < 3 * R.card →
        let s := step solve G x B ℓ k R
        s.1 ∪ s.2 = R ∧ s.2.Nonempty ∧ 2 * (s.2 \ s.1).card ≤ R.card ∧
          (∀ u ∈ s.1 \ s.2, ∀ v ∈ s.2 \ s.1, ¬G.Adj u v) ∧
          cost (fun v => (x v : ℝ)) (s.1 ∩ s.2) ≤
            4 * (ratio B n : ℝ) * s.1.card * s.2.card / (scale n ℓ k : ℝ) := by
  obtain ⟨K, hK, hforced⟩ := Lax263307.ForcedSeparation.certificate_separation C hereditary a A ha hA class_bound
  obtain ⟨solve, c, hpoly, hc, hsolve⟩ := Lax263307.VertexSplitting.split_certificate
  obtain ⟨B, hB, hratio⟩ := bounded_ratio c hc
  refine ⟨solve, K, B, hpoly, hK, hB, ?_⟩
  intro n G _ hG hn x k p ℓ hk hp hℓ hx hmass hedge htarget hsparsity R hlargeR
  let r := R.card
  let H := restriction G R
  let f : H ↪g G := embedding G R
  let y : Fin r → ℚ≥0 := fun v => x (f v)
  let ρ : ℝ := (ratio B n : ℝ)
  let γ : ℝ := (scale n ℓ k : ℝ)
  let large := largeCapacity B n r ℓ k
  have hrpos : 0 < r := by dsimp [r]; omega
  have hrn : r ≤ n := R.card_le_univ.trans_eq (Fintype.card_fin n)
  have hρeq : ρ = (B : ℝ) * ((Nat.log2 (2 * n) : ℝ) + 1) := by dsimp [ρ, ratio]; push_cast; rfl
  have hγeq : γ = (ℓ : ℝ) * (n : ℝ) ^ 2 / (3 * k) := by dsimp [γ, scale]; push_cast; rfl
  have hρ : 0 ≤ ρ := by rw [hρeq]; positivity
  have hγ : 0 < γ := by
    rw [hγeq]
    exact (remainder_scale n n ℓ hn hℓ k (by exact_mod_cast hk) (by omega)).1
  have hcap : ρ * (2 * r : ℕ) ^ 2 / γ < (large : ℝ) := by
    have h := Nat.le_ceil (ratio B n * (2 * r : ℕ) ^ 2 / scale n ℓ k)
    have hq : ratio B n * (2 * r : ℕ) ^ 2 / scale n ℓ k < (large : ℚ) := by
      change ratio B n * (2 * r : ℕ) ^ 2 / scale n ℓ k <
        ((Nat.ceil (ratio B n * (2 * r : ℕ) ^ 2 / scale n ℓ k) + 1 : ℕ) : ℚ)
      rw [Nat.cast_add, Nat.cast_one]
      linarith
    dsimp only [ρ, γ]
    exact_mod_cast hq
  obtain ⟨cert, hencoded, hadmissible, hflow, hcut⟩ := hsolve r H y large hrpos
  have hcut' : (ratioCost (splitInstance H y large).network
      (splitInstance H y large).weights cert.cut : ℝ) ≤ ρ * (cert.flow.value : ℝ) := by
    apply hcut.trans (mul_le_mul_of_nonneg_right _ (by positivity))
    rw [hρeq]
    exact hratio n r hrpos hrn
  have hxnonnegative (v : Fin n) : 0 ≤ (x v : ℝ) := by positivity
  have hscale : γ * k ≤ (ℓ : ℝ) * (r : ℝ) ^ 2 := by
    rw [hγeq]
    exact (remainder_scale n r ℓ hn hℓ k (by exact_mod_cast hk) hlargeR).2
  have hmass' : (∑ v : Fin r, (y v : ℝ)) ≤ k :=
    (sum_embedding f.toEmbedding (fun v => (x v : ℝ)) hxnonnegative).trans hmass
  have hedge' : edgeCost H (fun v => (y v : ℝ)) ≤ (k : ℝ) ^ 2 / p :=
    (edge_cost_embedding H G f (fun v => (x v : ℝ)) hxnonnegative).trans hedge
  obtain ⟨hleft, hright, hcover, hsep, hcost⟩ :=
    hforced r H (hereditary r n H G hG ⟨f⟩) hrpos y large cert ρ γ k p ℓ hℓ hρ hγ
      (by exact_mod_cast hk) (by exact_mod_cast hp) hscale (fun v => hx (f v)) hmass' hedge'
      htarget hsparsity hadmissible hflow hcut' hcap
  have hs := oriented H (fun v => (y v : ℝ)) ρ γ (leftShore cert.cut) (rightShore cert.cut)
    hleft hright hcover hsep hcost
  have honto : Finset.univ.image f = R := Finset.image_orderEmbOfFin_univ R rfl
  have hlift := lifted H G f R honto (fun v => (x v : ℝ)) ρ γ _ _
    hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2
  have hdecode : decodeCut (2 * R.card) (solve (encodeInput .directed
      (splitInstance (restriction G R) (fun v => x (label R v))
        (largeCapacity B n R.card ℓ k)))) = cert.cut := by
    change decodeCut (2 * r) (solve (encodeInput .directed (splitInstance H y large))) = cert.cut
    rw [hencoded, decode_cut_certificate]
  simp only [step, hdecode]
  exact hlift

theorem cuts_trace {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → ℝ) (ρ γ : ℝ)
    (cut : Finset (Fin n) → Finset (Fin n) × Finset (Fin n))
    (correct : ∀ R : Finset (Fin n), 2 * n < 3 * R.card →
      let s := cut R
      s.1 ∪ s.2 = R ∧ s.2.Nonempty ∧ 2 * (s.2 \ s.1).card ≤ R.card ∧
        (∀ u ∈ s.1 \ s.2, ∀ v ∈ s.2 \ s.1, ¬G.Adj u v) ∧
        cost x (s.1 ∩ s.2) ≤ 4 * ρ * s.1.card * s.2.card / γ)
    (fuel : ℕ) (start : Finset (Fin n)) (budget : start.card ≤ fuel) :
    ∃ T : Lax263307.CutTraces.Trace G start (cuts cut fuel start).length,
      3 * (T.remaining (cuts cut fuel start).length).card ≤ 2 * n ∧
      (∀ i : Fin (cuts cut fuel start).length,
        (T.left i, T.right i) = (cuts cut fuel start).get i) ∧
      ∀ i < (cuts cut fuel start).length,
        cost x (T.left i ∩ T.right i) ≤ 4 * ρ * (T.left i).card * (T.right i).card / γ := by
  induction fuel generalizing start with
  | zero =>
    refine ⟨Lax263307Proofs.CutTraces.emptyTrace G start, ?_, ?_, ?_⟩
    · change 3 * start.card ≤ 2 * n
      omega
    · intro i
      exact Fin.elim0 i
    · intro i hi
      simp [cuts] at hi
  | succ fuel ih =>
    by_cases hstop : 3 * start.card ≤ 2 * n
    · have hcs : cuts cut (fuel + 1) start = [] := by rw [cuts, if_pos hstop]
      rw [hcs]
      refine ⟨Lax263307Proofs.CutTraces.emptyTrace G start, hstop, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i hi
        simp at hi
    · have hs := correct start (lt_of_not_ge hstop)
      let s := cut start
      have hBsub : s.2 ⊆ start := by rw [← hs.1]; exact Finset.subset_union_right
      have hnext : s.1 \ s.2 = start \ s.2 := by
        rw [← hs.1]
        ext v
        simp only [Finset.mem_sdiff, Finset.mem_union]
        tauto
      have hcount := Finset.card_sdiff_add_card_eq_card hBsub
      have hpositive : 0 < s.2.card := Finset.card_pos.mpr hs.2.1
      have hbudget : (s.1 \ s.2).card ≤ fuel := by rw [hnext]; omega
      obtain ⟨T, hfinished, hmatches, hcosts⟩ := ih (s.1 \ s.2) hbudget
      have hcs : cuts cut (fuel + 1) start = s :: cuts cut fuel (s.1 \ s.2) := by
        rw [cuts, if_neg hstop]
      rw [hcs]
      refine ⟨Lax263307Proofs.CutTraces.prepend s.1 s.2 hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 T,
        hfinished, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · exact hmatches j
      · intro i hi
        cases i with
        | zero => exact hs.2.2.2.2
        | succ i => exact hcosts i (by simpa using hi)

theorem mem_separator {n : ℕ} (cs : List (Finset (Fin n) × Finset (Fin n))) (v : Fin n) :
    v ∈ Lax263307.ComputedSeparators.separator cs ↔ ∃ s ∈ cs, v ∈ s.1 ∩ s.2 := by
  induction cs with
  | nil => simp [Lax263307.ComputedSeparators.separator]
  | cons s cs ih =>
    simp only [Lax263307.ComputedSeparators.separator, List.foldr_cons, Finset.mem_union]
    change v ∈ s.1 ∩ s.2 ∨ v ∈ Lax263307.ComputedSeparators.separator cs ↔ _
    rw [ih]
    simp only [List.mem_cons, exists_eq_or_imp]

theorem separator_eq {n q : ℕ} (G : SimpleGraph (Fin n)) (start : Finset (Fin n))
    (cs : List (Finset (Fin n) × Finset (Fin n))) (hsize : cs.length = q)
    (T : Lax263307.CutTraces.Trace G start q)
    (agrees : ∀ i : Fin cs.length, (T.left i, T.right i) = cs.get i) :
    Lax263307.ComputedSeparators.separator cs = Lax263307.CutTraces.separator T := by
  ext v
  rw [mem_separator]
  simp only [Lax263307.CutTraces.separator, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨s, hs, hv⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hs
    have hm := (agrees i).trans hi
    refine ⟨⟨i.val, by rw [← hsize]; exact i.isLt⟩, ?_⟩
    change v ∈ T.left i.val ∩ T.right i.val
    have hl : T.left i.val = s.1 := congrArg Prod.fst hm
    have hr : T.right i.val = s.2 := congrArg Prod.snd hm
    rw [hl, hr]
    exact hv
  · rintro ⟨i, hv⟩
    let j : Fin cs.length := ⟨i.val, by rw [hsize]; exact i.isLt⟩
    refine ⟨cs.get j, List.get_mem cs j, ?_⟩
    rw [← agrees j]
    exact hv

theorem remaining_eq {n : ℕ} (G : SimpleGraph (Fin n)) (start : Finset (Fin n))
    (cs : List (Finset (Fin n) × Finset (Fin n)))
    (T : Lax263307.CutTraces.Trace G start cs.length)
    (agrees : ∀ i : Fin cs.length, (T.left i, T.right i) = cs.get i) :
    remaining start cs = T.remaining cs.length := by
  unfold remaining
  split_ifs with h
  · exact ((congrArg T.remaining h).trans T.initial).symm
  · let i : Fin cs.length := ⟨cs.length - 1, by omega⟩
    change (cs.get i).1 \ (cs.get i).2 = T.remaining cs.length
    rw [← agrees i]
    have hi : i.val + 1 = cs.length := by dsimp [i]; omega
    exact (T.next i i.isLt).symm.trans (congrArg T.remaining hi)

theorem pieces_eq {n : ℕ} (G : SimpleGraph (Fin n))
    (cs : List (Finset (Fin n) × Finset (Fin n)))
    (T : Lax263307.CutTraces.Trace G Finset.univ cs.length)
    (agrees : ∀ i : Fin cs.length, (T.left i, T.right i) = cs.get i) (i : Option (Fin cs.length)) :
    pieces cs i = Lax263307.CutTraces.parts T i := by
  cases i with
  | none => exact remaining_eq G Finset.univ cs T agrees
  | some i =>
    change (cs.get i).2 \ (cs.get i).1 = T.right i \ T.left i
    rw [← agrees i]

/--
---
conclusion: Lax263307.ComputedSeparators.light_separator
---
The fixed registered solver is called on canonically labeled remainders.
Its actual cut prefixes determine the entire bounded cut list. The resulting
computed parts are the vertices of the checked balanced partition.
-/
theorem light_separator (C : GraphClass) (hereditary : IsHereditary C)
    (a A : ℕ) (ha : 0 < a) (hA : 0 < A) (class_bound : HasPowerBagBound C a A) :
    ∃ (solve : List ℕ → List ℕ) (K B : ℕ), Lax759944.RamPolytime.RamPolytime solve ∧
      0 < K ∧ 0 < B ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G ∈ C n → 0 < n → ∀ (x : Fin n → ℚ≥0) (k p ℓ : ℕ),
      0 < k → 0 < p → 0 < ℓ →
      (∀ v, (x v : ℝ) ≤ 1) → (∑ v, (x v : ℝ)) ≤ k →
      edgeCost G (fun v => (x v : ℝ)) ≤ (k : ℝ) ^ 2 / p →
      (K : ℝ) * ((ℓ : ℝ) + 1) ^ (4 * a + 2) ≤ k →
      (2 * K : ℝ) * ((ℓ : ℝ) + 1) ^ (4 * a + 2) ≤ p →
      let cs := cuts (step solve G x B ℓ k) n Finset.univ
      cs.length ≤ n ∧
        Lax263307.EdgeSublinearSeparators.IsBalancedSeparator G
          (Lax263307.ComputedSeparators.separator cs) ∧
        cost (fun v => (x v : ℝ)) (Lax263307.ComputedSeparators.separator cs) ≤
          12 * (ratio B n : ℝ) * k / ℓ ∧
        ∃ P : Lax263307.SeparatorComponents.Partition G
            (Lax263307.ComputedSeparators.separator cs) (Option (Fin cs.length)),
          (∀ i, P.vertices i = pieces cs i) ∧ ∀ i, 3 * (P.vertices i).card ≤ 2 * n := by
  obtain ⟨solve, K, B, hpoly, hK, hB, hstep⟩ := exists_solver C hereditary a A ha hA class_bound
  refine ⟨solve, K, B, hpoly, hK, hB, ?_⟩
  intro n G _ hG hn x k p ℓ hk hp hℓ hx hmass hedge htarget hsparsity
  let cut := step solve G x B ℓ k
  let cs := cuts cut n Finset.univ
  have hcorrect := hstep n G hG hn x k p ℓ hk hp hℓ hx hmass hedge htarget hsparsity
  have hρ : 0 ≤ (ratio B n : ℝ) := by dsimp [ratio]; positivity
  have hγ : 0 < (scale n ℓ k : ℝ) := by
    have hpos : (0 : ℚ) < scale n ℓ k := by dsimp [scale]; positivity
    exact_mod_cast hpos
  have hxnonnegative (v : Fin n) : 0 ≤ (x v : ℝ) := by positivity
  obtain ⟨T, hfinished, hmatches, hcosts⟩ := cuts_trace G (fun v => (x v : ℝ))
    (ratio B n) (scale n ℓ k) cut hcorrect n Finset.univ (by simp)
  have h := Lax263307.CutTraces.trace_correct G T hfinished (fun v => (x v : ℝ))
    hxnonnegative (ratio B n) (scale n ℓ k) hρ hγ hcosts
  have heq := separator_eq G Finset.univ cs rfl T hmatches
  have hcosteq : 4 * (ratio B n : ℝ) * (n : ℝ) ^ 2 / (scale n ℓ k : ℝ) =
      12 * (ratio B n : ℝ) * k / ℓ := by
    dsimp only [scale]
    push_cast
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
    have hℓR : (ℓ : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hℓ)
    field_simp
    ring
  change cs.length ≤ n ∧ _
  rw [heq]
  refine ⟨h.1, h.2.1, by rw [← hcosteq]; exact h.2.2,
    Lax263307Proofs.CutTraces.partition T, ?_, ?_⟩
  · intro i
    exact (pieces_eq G cs T hmatches i).symm
  · intro i
    cases i with
    | none => exact hfinished
    | some i =>
      have hsmall := T.small_piece i i.isLt
      have hrem : (T.remaining i).card ≤ n := by simpa using Finset.card_le_univ (T.remaining i)
      change 3 * (T.right i \ T.left i).card ≤ 2 * n
      omega

end Lax263307Proofs.ComputedSeparators
