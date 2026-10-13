import Lax263307Proofs.NativeCatalogMetadata
import Mathlib.Data.Int.NatAbs

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeIntegerEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding

def sign (p q : ℕ) : ℕ := if p<q then 1 else 0

def magnitude (p q : ℕ) : ℕ := if p<q then q-p else p-q

theorem sign_le (p q : ℕ) : sign p q≤1 := by unfold sign; split_ifs <;> omega

theorem magnitude_bound (p q : ℕ) : magnitude p q≤max p q := by unfold magnitude; split_ifs <;> omega

theorem encoding (p q : ℕ) : encodeRational ((p : ℚ)-q)=[sign p q,magnitude p q,1] := by
  have he : (p : ℚ)-q=(((p : ℤ)-(q : ℤ) : ℤ) : ℚ) := by simp
  rw [he,encodeRational]
  simp only [Rat.num_intCast,Rat.den_intCast]
  have hsg : ((p : ℤ)-(q : ℤ)<0) ↔ p<q := by omega
  simp only [hsg,sign,magnitude]
  by_cases h : p<q
  · simp only [if_pos h,Int.natAbs_natCast_sub_natCast_of_le h.le]
  · simp only [if_neg h,Int.natAbs_natCast_sub_natCast_of_ge (by omega : q≤p)]

def normalize : Com := .ite (.lt (.var "coefficient.positive") (.var "coefficient.negative"))
  (.seq (.assign "coefficient.sign" (.lit 1))
    (.assign "coefficient.magnitude" (.sub (.var "coefficient.negative") (.var "coefficient.positive"))))
  (.seq (.assign "coefficient.sign" (.lit 0))
    (.assign "coefficient.magnitude" (.sub (.var "coefficient.positive") (.var "coefficient.negative"))))

theorem normalize_spec (B p q : ℕ) (h1 : 1<B) (hp : p<B) (hq : q<B) :
    Spec B (fun σ => σ.vars "coefficient.positive"=p ∧ σ.vars "coefficient.negative"=q) normalize
      (fun _ τ => τ.vars "coefficient.sign"=sign p q ∧ τ.vars "coefficient.magnitude"=magnitude p q) 10 := by
  by_cases h : p<q
  · run_vcg
    all_goals simp_all [Env.setVar,sign,magnitude]
  · run_vcg
    all_goals simp_all [Env.setVar,sign,magnitude]

def append : Com := .seq normalize
  (.seq (Lax455465Proofs.RamWordBuffer.append "lp.input" "lp.length" (.var "coefficient.sign"))
    (.seq (Lax455465Proofs.RamWordBuffer.append "lp.input" "lp.length" (.var "coefficient.magnitude"))
      (Lax455465Proofs.RamWordBuffer.append "lp.input" "lp.length" (.lit 1))))

theorem append_spec (B p q : ℕ) (front : List ℕ) (h1 : 1<B) (hp : p<B) (hq : q<B) (hlen : front.length+3<B) :
    Spec B (fun σ => σ.vars "coefficient.positive"=p ∧ σ.vars "coefficient.negative"=q ∧
      Prefix front "lp.input" σ ∧ σ.vars "lp.length"=front.length ∧ front.length+3≤(σ.arrs "lp.input").length)
      append (fun _ τ => Prefix (front++encodeRational ((p : ℚ)-q)) "lp.input" τ ∧ τ.vars "lp.length"=front.length+3) 31 := by
  rintro σ ⟨hpos,hneg,hprefix,hcount,hroom⟩
  obtain ⟨ν,r1,p1⟩ := normalize_spec B p q h1 hp hq σ ⟨hpos,hneg⟩
  have hs : sign p q<B := (sign_le p q).trans_lt h1
  have hm : magnitude p q<B := (magnitude_bound p q).trans_lt (max_lt hp hq)
  obtain ⟨μ,r2,p2⟩ := Lax455465Proofs.RamWordBuffer.append_spec B "lp.input" "lp.length" front (sign p q)
    (.var "coefficient.sign") h1 (by omega) ν
    ⟨by simpa only [Prefix,r1.frame_arr "lp.input" (by decide)] using hprefix,
      (r1.frame_var "lp.length" (by decide)).trans hcount,
      by rw [Lax455465Proofs.RamFrames.run_array_length r1]; omega,
      by rw [evalB_var_iff]; exact ⟨p1.1.symm,p1.1 ▸ hs⟩⟩
  have hlen1 : (front++[sign p q]).length=front.length+1 := by simp
  have hmag : μ.vars "coefficient.magnitude"=magnitude p q := (r2.frame_var "coefficient.magnitude" (by decide)).trans p1.2
  obtain ⟨ξ,r3,p3⟩ := Lax455465Proofs.RamWordBuffer.append_spec B "lp.input" "lp.length" (front++[sign p q]) (magnitude p q)
    (.var "coefficient.magnitude") h1 (by rw [hlen1]; omega) μ
    ⟨p2.1,by rw [hlen1]; exact p2.2,by rw [hlen1,Lax455465Proofs.RamFrames.run_array_length r2,Lax455465Proofs.RamFrames.run_array_length r1]; omega,
      by rw [evalB_var_iff]; exact ⟨hmag.symm,hmag ▸ hm⟩⟩
  have hlen2 : ((front++[sign p q])++[magnitude p q]).length=front.length+2 := by simp
  obtain ⟨τ,r4,p4⟩ := Lax455465Proofs.RamWordBuffer.append_spec B "lp.input" "lp.length" ((front++[sign p q])++[magnitude p q]) 1
    (.lit 1) h1 (by rw [hlen2]; omega) ξ
    ⟨p3.1,by simpa only [List.length_append,List.length_singleton,Nat.add_assoc] using p3.2,
      by rw [hlen2,Lax455465Proofs.RamFrames.run_array_length r3,Lax455465Proofs.RamFrames.run_array_length r2,Lax455465Proofs.RamFrames.run_array_length r1]; omega,
      evalB_lit h1⟩
  refine ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono (by simp [Expr.size]),?_,?_⟩
  · simpa only [encoding,List.append_assoc,List.cons_append,List.nil_append] using p4.1
  · simpa only [hlen2,Nat.add_assoc] using p4.2

end Lax263307Proofs.NativeIntegerEncoding
