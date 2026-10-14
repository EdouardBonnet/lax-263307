import Lax263307Proofs.NativeComponentCosts
import Lax263307Proofs.NativeSignedSum
import Lax263307Proofs.NativeSumHeight
import Lax263307Proofs.NativeSlice

namespace Lax263307Proofs.NativeComponentSum

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 ComputedSeparators NativeSignedArithmetic NativeRestrictionRead

def setup : Com := .seq (.assign "sum.count" (.var "restrict.count"))
  (.seq (.assign "fill.length" (.var "lp.position")) (.assign "slice.start" (.lit 0)))

def command : Com := .seq NativeComponentCosts.command (.seq setup
  (.seq (NativeSlice.command "lp.word" "sum.input") NativeSignedSum.command))

theorem setup_spec (B r : ℕ) (hB : 3*r+10<B) :
    Spec B (fun σ => σ.vars "restrict.count"=r ∧ σ.vars "lp.position"=3*r) setup
      (fun _ τ => τ.vars "sum.count"=r ∧ τ.vars "fill.length"=3*r ∧ τ.vars "slice.start"=0) 6 := by
  rintro σ ⟨hc,hp⟩
  run_vcg
  all_goals simp_all [Env.setVar]

theorem sum_labels {n : ℕ} (R : Finset (Fin n)) (x : Fin n → ℚ) :
    (List.ofFn (fun i : Fin R.card => x (label R i))).sum=∑ v∈R,x v := by
  have him : (Finset.univ : Finset (Fin R.card)).image (label R)=R :=
    Finset.image_orderEmbOfFin_univ R rfl
  calc
    _=∑ i : Fin R.card,x (label R i) := by simp [List.sum_ofFn]
    _=∑ v∈(Finset.univ : Finset (Fin R.card)).image (label R),x v :=
      (Finset.sum_image (by intro i hi j hj h; exact (label R).injective h)).symm
    _=∑ v∈R,x v := by rw [him]

/-- Compute a component's exact rational cost, with multiplicative
height bounds for all partial sums. -/
theorem command_spec (B M n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ) (R : Finset (Fin n)) (hM : 1≤M) (hN : 3*n+10<B)
    (hB : 2*((2*M)^(R.card+1))^2+3<B) (hx : ∀ v,Bounded M (x v)) :
    Spec B (fun σ => Data G x R σ ∧ 3*R.card<(σ.arrs "lp.word").length ∧
      3*R.card≤(σ.arrs "sum.input").length) command
      (fun _ τ => Data G x R τ ∧ RamRational.FractionOutput (∑ v∈R,x v) τ)
      ((36*(((2*M)^(R.card+1))^2).size+258)*R.card+38) := by
  let qs := List.ofFn (fun i : Fin R.card => x (label R i))
  let H := (2*M)^(R.card+1)
  have hlen : qs.length=R.card := by simp [qs]
  have hr := NativeMaskUnpack.card_bound R
  have hHM : M≤H := by
    calc
      M≤2*M := by omega
      _=(2*M)^1 := (pow_one _).symm
      _≤H := Nat.pow_le_pow_right (by omega) (by omega)
  have hHH : 2*H^2+3<B := hB
  have hHB : H<B := by nlinarith only [hHH,Nat.le_mul_self H]
  have hMB : M<B := hHM.trans_lt hHB
  have hqs : ∀ q∈qs,Bounded M q := by
    intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    exact hx _
  have hwords : ∀ z∈NativeRationalTabulate.words qs,z<B := by
    intro z hz
    obtain ⟨q,hq,hz⟩ := List.mem_flatMap.mp hz
    simp only [encodeRational,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl
    · split_ifs <;> omega
    · exact (hqs q hq).1.trans_lt hMB
    · exact (hqs q hq).2.trans_lt hMB
  rintro σ ⟨hd,hwordroom,hsumroom⟩
  obtain ⟨ν,r1,p1⟩ := NativeComponentCosts.command_spec B M n G x R hN hMB hx σ ⟨hd,hwordroom⟩
  obtain ⟨μ,r2,p2⟩ := setup_spec B R.card (by omega) ν ⟨p1.1.count,p1.2.2⟩
  have hp2 : Prefix (NativeRationalTabulate.words qs) "lp.word" μ := by
    simpa only [qs,NativeRationalTabulate.words,encodeVector,Prefix,r2.frame_arr "lp.word" (by decide)] using p1.2.1
  obtain ⟨ρ,r3,p3⟩ := NativeSlice.command_spec B "lp.word" "sum.input" [] (NativeRationalTabulate.words qs) [] (by decide)
    (by simp only [List.length_nil,NativeRationalTabulate.words_length,hlen,Nat.zero_add]; omega) hwords μ
    ⟨⟨by simpa only [List.nil_append,List.append_nil] using hp2,by simpa only [List.length_nil] using p2.2.2⟩,
      by simpa only [NativeRationalTabulate.words_length,hlen] using p2.2.1,
      by simpa only [NativeRationalTabulate.words_length,hlen,RamFrames.run_array_length r2,RamFrames.run_array_length r1] using hsumroom⟩
  obtain ⟨τ,r4,p4⟩ := NativeSignedSum.command_spec B H qs hB (by rw [hlen]; omega)
    (fun q hq => by simpa only [hlen] using NativeSumHeight.uniform_entry M qs hM hqs q hq)
    (fun i _ => by simpa only [hlen,NativeSignedSum.partialSum] using NativeSumHeight.uniform_partial M qs hM hqs i) ρ
    ⟨p3.2,by simpa only [hlen] using (r3.frame_var "sum.count" (by decide)).trans p2.1⟩
  have rr := r1.seq (r2.seq (r3.seq r4))
  refine ⟨τ,rr.mono ?_,frame rr hd (by decide) (by decide),?_⟩
  · simp only [NativeRationalTabulate.words_length,hlen]
    dsimp only [H]
    nlinarith only []
  · simpa only [qs,sum_labels] using p4.2

end Lax263307Proofs.NativeComponentSum
