import Lax263307Proofs.NativeDistanceInput
import Lax263307Proofs.NativeRationalBounds
import Lax455465Proofs.WordSize

namespace Lax263307Proofs.NativeDistanceQueryResources

open Lax455465Proofs Lax759944.BinaryWordEncoding
open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax263307.DistanceProjection NativeDistanceData

private theorem rational_words (M : ℕ) (q : ℚ) (hM : 1≤M)
    (hq : NativeSignedArithmetic.Bounded M q) : ∀ z∈encodeRational q,z≤M := by
  intro z hz
  simp only [encodeRational,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl | rfl | rfl
  · split_ifs <;> omega
  · exact hq.1
  · exact hq.2

private theorem vector_words {n : ℕ} (M : ℕ) (x : Fin n → ℚ) (hM : 1≤M)
    (hx : ∀ i,NativeSignedArithmetic.Bounded M (x i)) : ∀ z∈encodeVector x,z≤M := by
  intro z hz
  simp only [encodeVector,List.mem_flatMap,List.mem_ofFn] at hz
  obtain ⟨q,⟨i,rfl⟩,hz⟩ := hz
  exact rational_words M (x i) hM (hx i) z hz

/-- Dimensions and all rational fields control the actual encoded LP. -/
theorem program_words {m n : ℕ} (M : ℕ) (P : Program ℚ m n) (hM : 1≤M)
    (hm : m≤M) (hn : n≤M)
    (hA : ∀ i j,NativeSignedArithmetic.Bounded M (P.A i j))
    (hb : ∀ i,NativeSignedArithmetic.Bounded M (P.b i))
    (hc : ∀ i,NativeSignedArithmetic.Bounded M (P.c i)) :
    ∀ z∈encodeProgram P,z≤M := by
  intro z hz
  simp only [encodeProgram,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with ((hdim|hz)|hz)|hz
  · rcases hdim with rfl|rfl
    · exact hm
    · exact hn
  · obtain ⟨q,hq,hz⟩ := List.mem_flatMap.mp hz
    obtain ⟨row,hrow,hq⟩ := List.mem_flatten.mp hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hrow
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hq
    exact rational_words M _ hM (hA i j) z hz
  · exact vector_words M _ hM hb z hz
  · exact vector_words M _ hM hc z hz

/-- Each genuine rational source field inherits the encoded-word bound. -/
theorem source_fields {m n : ℕ} (B : ℕ) (P : Program ℚ m n)
    (hw : ∀ z∈encodeProgram P,z<B) :
    (∀ i j,Height B (P.A i j)) ∧ (∀ i,Height B (P.b i)) ∧ (∀ j,Height B (P.c j)) := by
  have rational (q : ℚ) (hq : ∀ z∈encodeRational q,z<B) : Height B q :=
    ⟨hq _ (by simp [encodeRational]),hq _ (by simp [encodeRational])⟩
  refine ⟨?_,?_,?_⟩
  · intro i j
    apply rational
    intro z hz
    apply hw z
    simp only [encodeProgram,List.mem_append]
    refine Or.inl (Or.inl (Or.inr ?_))
    apply List.mem_flatMap.mpr
    refine ⟨P.A i j,?_,hz⟩
    apply List.mem_flatten.mpr
    exact ⟨List.ofFn (P.A i),List.mem_ofFn.mpr ⟨i,rfl⟩,List.mem_ofFn.mpr ⟨j,rfl⟩⟩
  · intro i
    apply rational
    intro z hz
    apply hw z
    simp only [encodeProgram,List.mem_append]
    exact Or.inl (Or.inr (List.mem_flatMap.mpr ⟨P.b i,List.mem_ofFn.mpr ⟨i,rfl⟩,hz⟩))
  · intro j
    apply rational
    intro z hz
    apply hw z
    simp only [encodeProgram,List.mem_append]
    exact Or.inr (List.mem_flatMap.mpr ⟨P.c j,List.mem_ofFn.mpr ⟨j,rfl⟩,hz⟩)

def sizeBound (m n h : ℕ) : ℕ := wordLength m n*(h+m+2*n+4)

/-- A polynomial bit-size bound on the genuine distance-projection query,
using rational height rather than the numerical VM word bound. -/
theorem query_size {m n : ℕ} (h : ℕ) (P : Program ℚ m n) (x : Fin n → ℚ)
    (hb : NativeDistanceData.Bounded (2^h) P x) :
    bitSize (encodeProgram (distanceProgram P x))≤sizeBound m n h := by
  let E := h+m+2*n+2
  have hp : 2^h≤2^E := Nat.pow_le_pow_right (by decide) (by dsimp [E]; omega)
  have hrows : rows m n≤2^E := by
    exact (Nat.lt_two_pow_self.le).trans (Nat.pow_le_pow_right (by decide) (by dsimp [E,rows]; omega))
  have hcols : columns n≤2^E := by
    exact (Nat.lt_two_pow_self.le).trans (Nat.pow_le_pow_right (by decide) (by dsimp [E,columns]; omega))
  have hwords := program_words (2^E) (distanceProgram P x) Nat.one_le_two_pow hrows hcols
    (fun i j => ⟨(matrix_height _ P x hb i j).1.le.trans hp,(matrix_height _ P x hb i j).2.le.trans hp⟩)
    (fun i => ⟨(bound_height _ P x hb i).1.le.trans hp,(bound_height _ P x hb i).2.le.trans hp⟩)
    (fun j => ⟨(objective_height _ P x hb j).1.le.trans hp,(objective_height _ P x hb j).2.le.trans hp⟩)
  have hs := WordSize.bounded_size (encodeProgram (distanceProgram P x)) (E+1) (by
    intro z hz
    apply Nat.size_le.mpr
    have hh := hwords z hz
    rw [pow_succ]
    have ht := Nat.two_pow_pos E
    omega)
  simpa only [NativeDistanceInput.input_length,E,sizeBound,Nat.add_assoc] using hs

end Lax263307Proofs.NativeDistanceQueryResources
