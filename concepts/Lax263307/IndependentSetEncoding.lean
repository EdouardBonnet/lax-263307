import Lax263307.WeightedIndependentSet
import Lax560851.StructuralCombinators
import Lax759944.BinaryWordEncoding
import Mathlib.Data.List.OfFn

/-!
---
title: Canonical representations of weighted graphs and vertex sets
type: definition
---
An instance is represented by its order, row-major adjacency matrix, and
rational vertex weights in vertex order. Each rational contributes its sign,
absolute numerator, and positive denominator. The resulting list uses the
registered structural list presentation. A vertex set is represented by its
zero-one membership vector, whose length records the ambient graph order.

These encoders inspect only the supplied graph, weights, and vertex set.
The private injectivity proofs certify the representations without introducing
any graph or weight decoder into the mathematical problem.
-/

namespace Lax263307.IndependentSetEncoding

open WeightedIndependentSet
open Lax560851.StructuralPresentation Lax560851.StructuralCombinators
open Lax759944.BinaryWordEncoding (bitSize)
open scoped Classical

/-- Canonical sign, absolute numerator, and denominator of a rational. -/
def encodeRational (q : ℚ) : List ℕ :=
  [if q.num < 0 then 1 else 0, q.num.natAbs, q.den]

/-- The rational parameters in vertex order, followed by the accuracy. -/
def encodeParameters {n : ℕ} (w : Fin n → ℚ) (ε : ℚ) : List ℕ :=
  (List.ofFn w).flatMap encodeRational ++ encodeRational ε

/-- Total binary encoding length of the weights and the accuracy. -/
def rationalBitSize {n : ℕ} (w : Fin n → ℚ) (ε : ℚ) : ℕ :=
  bitSize (encodeParameters w ε)

/-- The full input word, including the row-major adjacency matrix. -/
def encodeInput {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Fin n → ℚ) (ε : ℚ) : List ℕ :=
  [n] ++ (List.ofFn fun u => List.ofFn fun v =>
    if G.Adj u v then 1 else 0).flatten ++ encodeParameters w ε

/-- The length-`n` membership vector of the selected independent set. -/
def encodeOutput {n : ℕ} (I : Finset (Fin n)) : List ℕ :=
  List.ofFn fun v => if v ∈ I then 1 else 0


/-- Canonical graph-and-weight packet, without the accuracy parameter. -/
noncomputable abbrev encodeInstance {n : ℕ} (G : SimpleGraph (Fin n))
    (w : Fin n → ℚ) : List ℕ :=
  [n] ++ (List.ofFn fun u => List.ofFn fun v =>
    if G.Adj u v then 1 else 0).flatten ++
    (List.ofFn w).flatMap encodeRational

/-- Equal-length blocks can be separated without interpreting their contents. -/
private theorem blocks_injective {α β : Type*} (f : α → List β) (k : ℕ)
    (length : ∀ a, (f a).length = k) (injective : Function.Injective f) :
    ∀ xs ys : List α, xs.length = ys.length → xs.flatMap f = ys.flatMap f → xs = ys
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => nomatch h
  | _ :: _, [], h, _ => nomatch h
  | x :: xs, y :: ys, hlength, h =>
      let fields := List.append_inj h ((length x).trans (length y).symm)
      congrArg₂ List.cons (injective fields.1)
        (blocks_injective f k length injective xs ys (Nat.succ.inj hlength) fields.2)

private theorem blocks_length {α β : Type*} (f : α → List β) (k : ℕ)
    (length : ∀ a, (f a).length = k) (xs : List α) :
    (xs.flatMap f).length = xs.length * k :=
  calc
    (xs.flatMap f).length = (xs.map fun a => (f a).length).sum := List.length_flatMap
    _ = (xs.map fun _ => k).sum := congrArg (fun g => (xs.map g).sum) (funext length)
    _ = (List.replicate xs.length k).sum := congrArg List.sum List.map_const
    _ = xs.length * k := List.sum_replicate _ _

private theorem flag_injective (p q : Prop) [Decidable p] [Decidable q]
    (h : (if p then 1 else 0 : ℕ) = if q then 1 else 0) : p ↔ q :=
  ⟨fun hp => not_not.mp (fun hq => Nat.one_ne_zero
      ((if_pos hp).symm.trans (h.trans (if_neg hq)))),
   fun hq => not_not.mp (fun hp => Nat.one_ne_zero
      ((if_pos hq).symm.trans (h.symm.trans (if_neg hp))))⟩

private theorem signed_integer_injective : ∀ a b : ℤ,
    (if a < 0 then 1 else 0 : ℕ) = (if b < 0 then 1 else 0) →
    a.natAbs = b.natAbs → a = b
  | .ofNat _, .ofNat _, _, habs => congrArg Int.ofNat habs
  | .negSucc _, .negSucc _, _, habs => congrArg Int.negSucc (Nat.succ.inj habs)
  | .ofNat a, .negSucc b, hsign, _ => False.elim (Nat.zero_ne_one
      ((if_neg (not_lt.mpr (Int.natCast_nonneg a))).symm.trans
        (hsign.trans (if_pos (Int.negSucc_lt_zero b)))))
  | .negSucc a, .ofNat b, hsign, _ => False.elim (Nat.one_ne_zero
      ((if_pos (Int.negSucc_lt_zero a)).symm.trans
        (hsign.trans (if_neg (not_lt.mpr (Int.natCast_nonneg b))))))

private theorem rational_injective : Function.Injective encodeRational :=
  fun a b h =>
    let fields := List.cons.inj h
    let rest := List.cons.inj fields.2
    Rat.ext (signed_integer_injective a.num b.num fields.1 rest.1)
      (List.cons.inj rest.2).1

private theorem matrix_blocks {n : ℕ} (G : SimpleGraph (Fin n)) :
    (List.ofFn fun u => List.ofFn fun v => if G.Adj u v then 1 else 0).flatten =
      (List.ofFn fun u v => if G.Adj u v then 1 else 0).flatMap List.ofFn :=
  (congrArg List.flatten (List.map_ofFn (f := fun (u v : Fin n) => (if G.Adj u v then 1 else 0 : ℕ))
    (g := fun f : Fin n → ℕ => List.ofFn f))).symm

private theorem matrix_length {n : ℕ} (G : SimpleGraph (Fin n)) :
    (List.ofFn fun u => List.ofFn fun v => if G.Adj u v then 1 else 0).flatten.length = n*n :=
  (congrArg List.length (matrix_blocks G)).trans
    ((blocks_length List.ofFn n (fun _ => List.length_ofFn) _).trans
      (congrArg (· * n) List.length_ofFn))

private theorem matrix_injective {n : ℕ} (G H : SimpleGraph (Fin n))
    (h : (List.ofFn fun u => List.ofFn fun v => if G.Adj u v then 1 else 0).flatten =
      (List.ofFn fun u => List.ofFn fun v => if H.Adj u v then 1 else 0).flatten) : G = H :=
  let rows := blocks_injective List.ofFn n (fun _ => List.length_ofFn)
    List.ofFn_injective _ _ (List.length_ofFn.trans List.length_ofFn.symm)
    ((matrix_blocks G).symm.trans (h.trans (matrix_blocks H)))
  SimpleGraph.ext (funext fun u => funext fun v => propext
    (flag_injective _ _ (congrFun (congrFun (List.ofFn_injective rows) u) v)))

private theorem weights_injective {n : ℕ} (w z : Fin n → ℚ)
    (h : (List.ofFn w).flatMap encodeRational = (List.ofFn z).flatMap encodeRational) : w = z :=
  List.ofFn_injective (blocks_injective encodeRational 3 (fun _ => rfl)
    rational_injective _ _ (List.length_ofFn.trans List.length_ofFn.symm) h)

/-- The canonical packet determines all three mathematical instance fields. -/
private theorem encodeInstance_injective : Function.Injective
    (fun x : Instance => encodeInstance x.graph x.weights) :=
  fun x y h =>
    let order : x.order = y.order := (List.cons.inj h).1
    match x, y, order, h with
    | ⟨n,G,w⟩, ⟨_,H,z⟩, rfl, h =>
      let fields := List.append_inj (List.cons.inj h).2
        ((matrix_length G).trans (matrix_length H).symm)
      congrArg₂ (Instance.mk n) (matrix_injective G H fields.1) (weights_injective w z fields.2)

private theorem list_injective :
    ∀ xs ys : List ℕ, listToRaw nat xs = listToRaw nat ys → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | _ :: xs, _ :: ys, h =>
      let fields := Lax560851.StructuralPresentation.Raw.pair.inj h
      congrArg₂ List.cons (Lax560851.StructuralPresentation.Raw.nat.inj fields.1)
        (list_injective xs ys fields.2)

/-- The standard structural-list representation of a weighted graph. -/
noncomputable def input : Presentation Instance :=
  presentationOf (fun x => listToRaw nat (encodeInstance x.graph x.weights))

/-- Distinct mathematical instances have distinct structural representations. -/
theorem input_faithful : input.Faithful :=
  fun _ _ h => encodeInstance_injective (list_injective _ _ h)

/-- A solution is written as its membership vector. -/
def output (s : Solution) : List ℕ := encodeOutput s.2

/-- The vector's length and entries determine its ambient set and vertices. -/
theorem output_injective : Function.Injective output :=
  fun ⟨n,_I⟩ ⟨m,J⟩ h =>
    let order : n = m := List.length_ofFn.symm.trans
      ((congrArg List.length h).trans List.length_ofFn)
    match m, order, J, h with
    | _, rfl, _J, h =>
      congrArg (Sigma.mk n) (Finset.ext (fun v => flag_injective _ _
        (congrFun (List.ofFn_injective h) v)))

end Lax263307.IndependentSetEncoding
