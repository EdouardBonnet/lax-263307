import Lax455465Proofs.RamLpRationalRead
import Lax455465Proofs.RamFractionPrimitives
import Lax263307Proofs.NativeMomentInput

/-!
A canonical rational reader whose input-buffer name is an explicit
code parameter.
-/

namespace Lax263307Proofs.NativeRationalRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamRational Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax455465Proofs.RamLpRationalRead

def command (array : String) : Com := .seq (.assign "rat.s" (.get array (.var "read.cursor")))
  (.seq (.assign "rat.n" (.get array (.add (.var "read.cursor") (.lit 1))))
    (.seq (.assign "rat.d" (.get array (.add (.var "read.cursor") (.lit 2))))
      (.assign "read.cursor" (.add (.var "read.cursor") (.lit 3)))))

theorem command_spec (B : ℕ) (array : String) (q : ℚ) (front tail : List ℕ) (h3 : 3 < B)
    (hlen : front.length+3 < B) (hn : q.num.natAbs < B) (hd : q.den < B) :
    Spec B (fun σ => Prefix (front++(encodeRational q++tail)) array σ ∧ σ.vars "read.cursor"=front.length)
      (command array) (fun _ τ => FractionOutput q τ ∧ τ.vars "read.cursor"=front.length+3) 17 := by
  have hsign : sign q < B := by unfold sign; split_ifs <;> omega
  have hsign1 : sign q ≤ 1 := by unfold sign; split_ifs <;> omega
  have hvalue := value_eq q
  rintro σ ⟨hp,hcursor⟩
  let words := front++(encodeRational q++tail)
  have hiS : front.length < words.length := by simp [words,encodeRational]
  have hiN : front.length+1 < words.length := by simp [words,encodeRational]
  have hiD : front.length+2 < words.length := by simp [words,encodeRational]
  have hoS : words[front.length]?=some (sign q) := by
    rw [List.getElem?_append_right (by omega),Nat.sub_self]
    simp [encodeRational,sign]
  have hoN : words[front.length+1]?=some q.num.natAbs := by
    rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
    simp [encodeRational]
  have hoD : words[front.length+2]?=some q.den := by
    rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
    simp [encodeRational]
  rw [List.getElem?_eq_getElem hiS] at hoS
  rw [List.getElem?_eq_getElem hiN] at hoN
  rw [List.getElem?_eq_getElem hiD] at hoD
  have hgetS := (hp front.length hiS).trans hoS
  have hgetN := (hp (front.length+1) hiN).trans hoN
  have hgetD := (hp (front.length+2) hiD).trans hoD
  have hroom : front.length+2 < (σ.arrs array).length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hgetD
    cases hgetD
  run_vcg
  all_goals simp_all [FractionOutput]

/-- Locate a rational entry inside a prefixed vector, without requiring
any particular values in the rest of the reserved native buffer. -/
theorem vector_entry_spec (B : ℕ) (array : String) (front tail : List ℕ) (qs : List ℚ)
    (i : ℕ) (hi : i < qs.length) (h3 : 3 < B) (hlen : front.length+3*i+3 < B)
    (hn : qs[i].num.natAbs < B) (hd : qs[i].den < B) :
    Spec B (fun σ => Prefix (front++(NativeRationalTabulate.words qs++tail)) array σ ∧
      σ.vars "read.cursor"=front.length+3*i) (command array)
      (fun _ τ => FractionOutput qs[i] τ ∧ τ.vars "read.cursor"=front.length+3*i+3) 17 := by
  have he : qs=qs.take i++qs[i]::qs.drop (i+1) := by
    rw [←List.drop_eq_getElem_cons hi,List.take_append_drop]
  have hlen' : (front++NativeRationalTabulate.words (qs.take i)).length=front.length+3*i := by
    rw [List.length_append,NativeRationalTabulate.words_length,List.length_take,Nat.min_eq_left hi.le]
  have hew : front++(NativeRationalTabulate.words qs++tail)=
      (front++NativeRationalTabulate.words (qs.take i))++
        (encodeRational qs[i]++(NativeRationalTabulate.words (qs.drop (i+1))++tail)) := by
    conv_lhs => rw [he]
    simp only [NativeRationalTabulate.words,List.flatMap_append,List.flatMap_cons,List.append_assoc]
  have hh := command_spec B array qs[i] (front++NativeRationalTabulate.words (qs.take i))
    (NativeRationalTabulate.words (qs.drop (i+1))++tail) h3 (by rwa [hlen']) hn hd
  simpa only [hlen',←hew] using hh

end Lax263307Proofs.NativeRationalRead
