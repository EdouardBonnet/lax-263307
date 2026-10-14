import Lax263307Proofs.NativeImageOutput
import Lax263307Proofs.NativeBlowUp
import Lax263307Proofs.NativeProgramCache
import Lax263307.PositiveWeights

namespace Lax263307Proofs.NativeWeightedOutput

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 WeightedAlgorithm IndependentBlowUp WeightedIndependentSet

abbrev owner {n : ℕ} (copies : Fin n → ℕ) (i : Fin (∑ v,copies v)) : Fin n := (labeling copies i).1

theorem owner_words {n : ℕ} (copies : Fin n → ℕ) :
    NativeBlowUp.owners copies=List.ofFn (fun i => (owner copies i).val) := by
  apply List.ext_getElem (by simp [NativeBlowUp.owners_length])
  intro i hi hj
  have hin : i<∑ v,copies v := by simpa only [NativeBlowUp.owners_length] using hi
  have hh := NativeBlowUp.owners_labeling copies ⟨i,hin⟩
  rw [List.getElem?_eq_getElem hi] at hh
  rw [List.getElem_ofFn]
  exact Option.some.inj hh

theorem projected {n : ℕ} (copies : Fin n → ℕ) (I : Finset (Fin (∑ v,copies v))) :
    I.image (owner copies)=project (I.image (labeling copies)) := by
  simp only [project,Finset.image_image]
  rfl

def metadata : Com := .seq (.assign "image.n" (.var "input.n"))
  (.seq (.assign "image.count" (.var "blowup.length")) (.assign "image.mask" (.var "root.mask")))

def command : Com := .seq metadata (.seq
  (NativeProgramCache.copy "blowup.owner" "image.labels" "image.count") NativeImageOutput.command)

private theorem value {B x : ℕ} {name : String} {σ : Env} (hx : σ.vars name=x) (hB : x<B) :
    (Expr.var name).evalB B σ=some x := by
  rw [evalB_var_iff]; exact ⟨hx.symm,hx ▸ hB⟩

/-- Project the actual blow-up answer through its stored copy-owner table,
then emit the full original-order membership vector. -/
theorem command_spec {n : ℕ} (B : ℕ) (copies : Fin n → ℕ) (I : Finset (Fin (∑ v,copies v)))
    (hB : n+(∑ v,copies v)+5<B) (hm : 2^(∑ v,copies v)<B) :
    Spec B (fun σ => σ.vars "input.n"=n ∧ σ.vars "blowup.length"=∑ v,copies v ∧
      σ.vars "root.mask"=NativeMasks.mask I ∧ Prefix (NativeBlowUp.owners copies) "blowup.owner" σ ∧
      (∑ v,copies v)≤(σ.arrs "image.labels").length ∧ (σ.arrs "image.output").length=n)
      command (fun σ τ => τ.out=σ.out++encodeOutput (project (I.image (labeling copies))))
      (24*n+44*(∑ v,copies v)+36) := by
  rintro σ ⟨hn,hN,hmask,howners,hroom,houtput⟩
  let N := ∑ v,copies v
  let σ1 := σ.setVar "image.n" n
  let σ2 := σ1.setVar "image.count" N
  let σ3 := σ2.setVar "image.mask" (NativeMasks.mask I)
  have r1 : Run B (.assign "image.n" (.var "input.n")) σ σ1 2 := Run.assign (value hn (by omega))
  have r2 : Run B (.assign "image.count" (.var "blowup.length")) σ1 σ2 2 := Run.assign (value (by simpa [σ1] using hN) (by omega))
  have r3 : Run B (.assign "image.mask" (.var "root.mask")) σ2 σ3 2 := Run.assign
    (value (by simpa [σ2,σ1] using hmask) ((NativeMasks.mask_bound I).trans hm))
  have rm : Run B metadata σ σ3 6 := r1.seq (r2.seq r3)
  have hwords : ∀ z∈NativeBlowUp.owners copies,z<B := by
    rw [owner_words copies]
    intro z hz
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
    exact (owner copies i).isLt.trans (by omega)
  obtain ⟨ν,rc,pc⟩ := NativeProgramCache.copy_spec B "blowup.owner" "image.labels" "image.count"
    (NativeBlowUp.owners copies) (by decide) (by simp [NativeBlowUp.owners_length]; omega) hwords σ3
    ⟨by simpa only [Prefix,σ3,σ2,σ1,arrs_setVar] using howners,
      by simp [σ3,σ2,σ1,N,NativeBlowUp.owners_length],
      by simpa only [NativeBlowUp.owners_length,σ3,σ2,σ1,arrs_setVar] using hroom⟩
  have hc : NativeImageOutput.Context (owner copies) I ν := by
    refine ⟨?_,?_,?_,?_,?_⟩
    · simpa [σ3,σ2,σ1] using rc.frame_var "image.n" (by decide)
    · simpa [σ3,σ2,σ1] using rc.frame_var "image.count" (by decide)
    · simpa [σ3,σ2,σ1] using rc.frame_var "image.mask" (by decide)
    · simpa only [owner_words copies] using pc.2
    · rw [RamFrames.run_array_length rc]
      simpa only [σ3,σ2,σ1,arrs_setVar] using houtput
  obtain ⟨τ,ri,pi⟩ := NativeImageOutput.command_spec B (owner copies) I hB hm ν hc
  refine ⟨τ,(rm.seq (rc.seq ri)).mono (by simp only [NativeBlowUp.owners_length]; omega),?_⟩
  have hout : ν.out=σ.out := (rc.out_eq (by decide)).trans (rm.out_eq (by decide))
  simpa only [hout,projected copies I] using pi

/-- Copies of nonpositive vertices do not exist, so projection already
has the same result as the functional solver's nonpositive-weight filter. -/
theorem discard_projected {n : ℕ} (weights : Fin n → ℚ) (ε : ℚ)
    (I : Finset (Fin (∑ v,WeightRounding.copies (PositiveWeights.positiveWeights weights) ε v))) :
    PositiveWeights.discardNonpositive weights (project (I.image
      (labeling (WeightRounding.copies (PositiveWeights.positiveWeights weights) ε))))=
      project (I.image (labeling (WeightRounding.copies (PositiveWeights.positiveWeights weights) ε))) := by
  let copies := WeightRounding.copies (PositiveWeights.positiveWeights weights) ε
  have hpositive : ∀ v∈project (I.image (labeling copies)),0<weights v := by
    intro v hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
    by_contra hnonpos
    have hw : weights u.1≤0 := by linarith
    have hz : copies u.1=0 := by
      simp [copies,WeightRounding.copies,WeightRounding.roundedCopies,PositiveWeights.positiveWeights,max_eq_right hw]
    have hh : 0<copies u.1 := Nat.zero_lt_of_lt u.2.isLt
    omega
  ext v
  simp only [PositiveWeights.discardNonpositive,Finset.mem_filter]
  exact ⟨And.left,fun hv => ⟨hv,hpositive v hv⟩⟩

end Lax263307Proofs.NativeWeightedOutput
