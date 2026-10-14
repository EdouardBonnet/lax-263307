import Lax263307Proofs.NativeMomentValue
import Lax263307Proofs.NativeSlice
import Lax455465Proofs.RamVectorEncoding

namespace Lax263307Proofs.NativeMomentStorage

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.RationalEncoding
open Lax263307 NativeSignedArithmetic NativeCatalogMetadata

def setup : Com := .seq (.assign "slice.start" (.lit 0))
  (.assign "fill.length" (.mul (.lit 3) (.var "catalog.count")))

def command : Com := .seq setup (NativeSlice.command "lp.word" "near.moments")

/-- Preserve the actual nearby LP point in the buffer read by the
conditioning search, in exactly the moment catalog's coordinate order. -/
theorem command_spec (B M n r : ℕ) (x : Fin (N n r) → ℚ)
    (hN : 3*N n r+10<B) (hM : M<B) (hx : ∀ i,Bounded M (x i)) :
    Spec B (fun σ => Prefix (encodeVector x) "lp.word" σ ∧
      Prefix (Lax263307.NativeCatalog.words n r) "catalog.mask" σ ∧
      σ.vars "catalog.count"=N n r ∧ 3*N n r≤(σ.arrs "near.moments").length) command
      (fun _ τ => NativeMomentValue.Context (MomentLP.decode x) τ ∧ Prefix (encodeVector x) "lp.word" τ)
      (48*N n r+12) := by
  have hlen : (encodeVector x).length=3*N n r := by
    change (RamVectorEncoding.encode (List.ofFn x)).length=_
    rw [RamVectorEncoding.length_encode,List.length_ofFn]
  have hsetup : Spec B (fun σ => σ.vars "catalog.count"=N n r) setup
      (fun _ τ => τ.vars "slice.start"=0 ∧ τ.vars "fill.length"=3*N n r) 6 := by
    run_vcg
    all_goals simp_all
  rintro σ ⟨hp,hkeys,hcount,hroom⟩
  obtain ⟨ν,r1,p1⟩ := hsetup σ hcount
  have hpν : Prefix (encodeVector x) "lp.word" ν := by
    simpa only [Prefix,r1.frame_arr "lp.word" (by decide)] using hp
  obtain ⟨τ,r2,p2⟩ := NativeSlice.command_spec B "lp.word" "near.moments" [] (encodeVector x) []
    (by decide) (by rw [List.length_nil,hlen]; omega)
    (NativeRationalBounds.vector_words B M (N n r) x (by omega) hM hx) ν
    ⟨⟨by simpa using hpν,by simpa using p1.1⟩,by simpa only [hlen] using p1.2,
      by rw [hlen,RamFrames.run_array_length r1]; exact hroom⟩
  have rr := r1.seq r2
  refine ⟨τ,rr.mono (by rw [hlen]; omega),⟨?_,?_,?_⟩,?_⟩
  · simpa only [Prefix,rr.frame_arr "catalog.mask" (by decide)] using hkeys
  · simpa only [NativeMomentValue.values_decode] using p2.2
  · exact (rr.frame_var "catalog.count" (by decide)).trans hcount
  · simpa only [List.nil_append,List.append_nil] using p2.1.1

end Lax263307Proofs.NativeMomentStorage
