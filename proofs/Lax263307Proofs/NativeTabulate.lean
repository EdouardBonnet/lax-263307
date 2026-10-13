import Lax263307Proofs.NativeCatalog

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeTabulate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState

def append (array : String) : Com :=
  Lax455465Proofs.RamWordBuffer.append array "fill.i" (.var "fill.value")

def command (array : String) (read : Com) : Com := .seq (.assign "fill.i" (.lit 0))
  (.while (.lt (.var "fill.i") (.var "fill.length")) (.seq read (append array)))

def Invariant (array : String) (P : Env → Prop) (xs : List ℕ) (σ : Env) : Prop :=
  P σ ∧ σ.vars "fill.length"=xs.length ∧ σ.vars "fill.i"≤xs.length ∧
  xs.length≤(σ.arrs array).length ∧ Prefix (xs.take (σ.vars "fill.i")) array σ

/-- Fill a reserved array using actual bounded native entry computations. -/
theorem command_spec (B : ℕ) (xs : List ℕ) (array : String) (P : Env → Prop) (read : Com) (K : ℕ)
    (hB : xs.length+1<B) (hwords : ∀ x∈xs,x<B)
    (hri : "fill.i"∉read.wvars) (hrl : "fill.length"∉read.wvars) (hra : array∉read.warrs)
    (hinit : ∀ σ,P σ → P (σ.setVar "fill.i" 0))
    (hwrite : ∀ σ τ,Run B (append array) σ τ 7 → P σ → P τ)
    (hread : ∀ i (hi : i<xs.length), Spec B (fun σ => P σ ∧ σ.vars "fill.i"=i) read
      (fun _ τ => P τ ∧ τ.vars "fill.value"=xs[i]) K) :
    Spec B (fun σ => P σ ∧ σ.vars "fill.length"=xs.length ∧ xs.length≤(σ.arrs array).length)
      (command array read) (fun _ τ => P τ ∧ Prefix xs array τ) ((K+11)*xs.length+6) := by
  have h1 : 1<B := by omega
  have hbody : Spec B (fun σ => Invariant array P xs σ ∧ σ.vars "fill.i"<xs.length)
      (.seq read (append array))
      (fun σ τ => Invariant array P xs τ ∧ τ.vars "fill.i"=σ.vars "fill.i"+1) (K+7) := by
    rintro σ ⟨⟨hPσ,hlen,hle,hroom,hprefix⟩,hlt⟩
    let i := σ.vars "fill.i"
    have htlen : (xs.take i).length=i := by rw [List.length_take,Nat.min_eq_left hle]
    obtain ⟨ν,r1,p1⟩ := hread i hlt σ ⟨hPσ,rfl⟩
    have hiν : ν.vars "fill.i"=i := r1.frame_var "fill.i" hri
    obtain ⟨τ,r2,p2⟩ := Lax455465Proofs.RamWordBuffer.append_spec B array "fill.i" (xs.take i) xs[i]
      (.var "fill.value") h1 (by rw [htlen]; omega) ν
      ⟨by simpa only [Prefix,r1.frame_arr array hra] using hprefix,by rwa [htlen],
        by rw [htlen,Lax455465Proofs.RamFrames.run_array_length r1]; omega,
        by rw [evalB_var_iff]; exact ⟨p1.2.symm,p1.2 ▸ hwords _ (List.getElem_mem hlt)⟩⟩
    have r2' : Run B (append array) ν τ 7 := r2
    have ht : τ.vars "fill.i"=i+1 := by simpa only [htlen] using p2.2
    have rr := r1.seq r2'
    refine ⟨τ,rr,⟨hwrite ν τ r2' p1.1,?_,by rw [ht]; omega,?_,?_⟩,ht⟩
    · exact (r2'.frame_var "fill.length" (by simp [append,Lax455465Proofs.RamWordBuffer.append,Com.wvars])).trans
        ((r1.frame_var "fill.length" hrl).trans hlen)
    · rwa [Lax455465Proofs.RamFrames.run_array_length rr]
    · rw [ht,List.take_succ_eq_append_getElem hlt]
      exact p2.1
  have hloop := Spec.forRangeZero "fill.i" "fill.length" (Invariant array P xs) xs.length (K+7)
    (by omega) (fun _ h => h.2.2.1) (fun _ h => h.2.1) hbody
  rintro σ ⟨hP,hlen,hroom⟩
  have hi : Invariant array P xs (σ.setVar "fill.i" 0) := by
    refine ⟨hinit σ hP,?_,by simp,hroom,?_⟩
    · simpa only [vars_setVar,String.reduceEq,if_false] using hlen
    · simp only [vars_setVar,if_true,List.take_zero,Prefix,List.length_nil]
      intro i hi
      omega
  obtain ⟨τ,rr,p⟩ := hloop σ hi
  refine ⟨τ,rr.mono (by nlinarith),p.1.1,?_⟩
  simpa only [p.2,List.take_length] using p.1.2.2.2.2

end Lax263307Proofs.NativeTabulate
