import Lax263307.IndependentSetProblem
import Lax455465Proofs.WordSize
import Mathlib.Tactic

namespace Lax263307Proofs.StructuralPacket

open Lax560851 StructuralPresentation StructuralCombinators WordArena
open Lax759944.BinaryWordEncoding (bitSize)
open Lax455465Proofs.WordSize

def triples (xs : List ℕ) : List ℕ := xs.flatMap fun x => [0,x,0]

def tape (k : ℕ) (xs : List ℕ) : List ℕ :=
  (encode (prod nat (list nat)) (k,xs)).toInput

def size (xs : List ℕ) : ℕ := bitSize ((encode (list nat) xs).toInput)

theorem into_size (r : StructuralPresentation.Raw) (m : WordMemory) :
    (encodeInto r m).1.size = m.size+3*r.nodes := by
  induction r generalizing m with
  | nat n => simp [encodeInto, StructuralPresentation.Raw.nodes] <;> omega
  | pair a b iha ihb =>
    simp only [encodeInto, Array.size_push, ihb, iha, StructuralPresentation.Raw.nodes]
    omega

theorem into_root (r : StructuralPresentation.Raw) (m : WordMemory) :
    (encodeInto r m).2+3 = (encodeInto r m).1.size := by
  cases r <;> simp [encodeInto]

theorem list_nodes (xs : List ℕ) : (listToRaw nat xs).nodes = 2*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change 1+(listToRaw nat xs).nodes+1 = 2*(xs.length+1)+1
    rw [ih]
    omega

theorem list_prefix (xs : List ℕ) (m : WordMemory) :
    ∃ rest, (encodeInto (listToRaw nat xs) m).1.toList = m.toList ++ triples xs ++ rest := by
  induction xs generalizing m with
  | nil => exact ⟨[0,0,0], by simp [listToRaw, encodeInto, triples, WordImage.natTag]⟩
  | cons x xs ih =>
    obtain ⟨rest, hr⟩ := ih (m.push 0 |>.push x |>.push 0)
    refine ⟨rest ++ [1,m.size,(encodeInto (listToRaw nat xs) (m.push 0 |>.push x |>.push 0)).2], ?_⟩
    change (((encodeInto (listToRaw nat xs) (m.push 0 |>.push x |>.push 0)).1.push 1
      |>.push m.size |>.push _).toList = _)
    simp only [Array.toList_push, hr]
    simp [triples, List.append_assoc, WordImage.natTag]

theorem tape_prefix (k : ℕ) (xs : List ℕ) :
    ∃ rest, tape k xs = (6*xs.length+6)::0::k::0::(triples xs ++ rest) := by
  obtain ⟨rest, hr⟩ := list_prefix xs #[0,k,0]
  have hs := into_size (listToRaw nat xs) #[0,k,0]
  rw [list_nodes] at hs
  have hs' : (encodeInto (listToRaw nat xs) #[0,k,0]).1.size = 6*xs.length+6 := by
    simpa using hs.trans (by simp; omega)
  refine ⟨rest ++ [1,0,(encodeInto (listToRaw nat xs) #[0,k,0]).2], ?_⟩
  change (encodeInto (listToRaw nat xs) #[0,k,0]).1.size ::
    (((encodeInto (listToRaw nat xs) #[0,k,0]).1.push 1 |>.push 0 |>.push _).toList) = _
  simp only [Array.toList_push, hr, hs']
  simp [List.append_assoc, list, WordImage.natTag]

theorem tape_length (k : ℕ) (xs : List ℕ) : (tape k xs).length = 6*xs.length+10 := by
  rw [tape, encode_toInput_length]
  change 3*(1+(listToRaw nat xs).nodes+1)+1 = _
  rw [list_nodes]
  omega

theorem packet_length (xs : List ℕ) : ((encode (list nat) xs).toInput).length = 6*xs.length+4 := by
  rw [encode_toInput_length]
  simp only [Presentation.structuralSize, list, list_nodes]
  omega

theorem length_le_size (xs : List ℕ) : 6*xs.length+4 ≤ size xs := by
  have h := length_le ((encode (list nat) xs).toInput)
  simpa only [packet_length, size] using h

theorem bitSize_triples (xs : List ℕ) : bitSize xs ≤ bitSize (triples xs) := by
  induction xs with
  | nil => exact le_rfl
  | cons x xs ih =>
    simp only [triples, List.flatMap_cons, List.cons_append, List.nil_append, bitSize_cons]
    change x.size+1+bitSize xs ≤ (0:ℕ).size+1+(x.size+1+((0:ℕ).size+1+bitSize (triples xs)))
    omega

theorem bits_le_size (xs : List ℕ) : bitSize xs ≤ size xs := by
  obtain ⟨rest, hr⟩ := list_prefix xs #[]
  have h := bitSize_triples xs
  unfold size encode encodeRaw WordImage.toInput
  simp only [list, bitSize_cons, hr, Array.toList_empty, List.nil_append, bitSize_append]
  omega

theorem accuracy_encoding (k : ℕ) :
    Lax263307.WeightedIndependentSet.encodeRational (1/((k:ℚ)+1)) = [0,1,k+1] := by
  have hp : 0 < k+1 := by omega
  have hn := Rat.inv_natCast_num_of_pos hp
  have hd := Rat.inv_natCast_den_of_pos hp
  simp only [Nat.cast_add, Nat.cast_one] at hn hd
  simp [Lax263307.WeightedIndependentSet.encodeRational, one_div, hn, hd]

theorem bits_accuracy (k : ℕ) : bitSize [0,1,k+1] ≤ k+6 := by
  simp only [bitSize_cons, bitSize_nil]
  have h : (k+1).size ≤ k+1 := Nat.size_le.mpr Nat.lt_two_pow_self
  norm_num at *
  omega

theorem list_payloads (xs : List ℕ) (w : ℕ) (h : ∀ x ∈ xs, x < 2^w) :
    (listToRaw nat xs).maxNat < 2^w := by
  induction xs with
  | nil => exact Nat.two_pow_pos _
  | cons x xs ih =>
    change max x (listToRaw nat xs).maxNat < 2^w
    exact max_lt (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

/-- The arena words and its tape length fit in this explicit width. -/
theorem tape_fits (k : ℕ) (xs : List ℕ) (w : ℕ) (hw : size xs+k+10 ≤ w) :
    Lax759944.RamPolytime.FitsInWords w ((tape k xs).length :: tape k xs) := by
  have hlen := length_le_size xs
  have hbits := bits_le_size xs
  have hval : ∀ x ∈ xs, x < 2^w := by
    intro x hx
    exact (member_bound xs x hx).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hk : k < 2^w := (by omega : k ≤ w).trans_lt Nat.lt_two_pow_self
  have hn : 6*xs.length+10 < 2^w := (by omega : 6*xs.length+10 ≤ w).trans_lt Nat.lt_two_pow_self
  have hf := encode_fits (prod nat (list nat)) (k,xs) w
    (show max k (listToRaw nat xs).maxNat < 2^w from max_lt hk (list_payloads xs w hval))
    (by
      change 3*(1+(listToRaw nat xs).nodes+1) ≤ 2^w
      rw [list_nodes]
      omega)
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · rwa [tape_length]
  · exact hf.2 x hx

end Lax263307Proofs.StructuralPacket
