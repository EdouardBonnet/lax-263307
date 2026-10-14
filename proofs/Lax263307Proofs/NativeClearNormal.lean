import Lax263307Proofs.NativeCutVector
import Lax263307Proofs.NativeDenominatorProduct
import Lax263307Proofs.NativeSlice

namespace Lax263307Proofs.NativeClearNormal

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.RationalEncoding
open Lax263307.RationalCutBuffer NativeSignedArithmetic

def setup : Com := .seq (.assign "slice.start" (.lit 0))
  (.assign "fill.length" (.mul (.lit 3) (.var "projection.n")))

def command : Com := .seq setup (.seq (NativeSlice.command "lp.word" "cut.source")
  (.seq NativeDenominatorProduct.command NativeCutVector.command))

/-- Convert the actual rational normal in the projection buffer to the
canonical rational encoding of its exact integer clearing. The two scans
and the copy have linear source cost; big integers stay in bounded RAM
words whose required length is controlled by the denominator product. -/
theorem command_spec (B M n : ℕ) (a : Fin n → ℚ)
    (hB : M*denominator a+M+denominator a+3*n+10<B) (ha : ∀ j,Bounded M (a j)) :
    Spec B (fun σ => Prefix (encodeVector a) "lp.word" σ ∧ σ.vars "projection.n"=n ∧
      3*n≤(σ.arrs "cut.source").length ∧ 3*n<(σ.arrs "lp.word").length) command
      (fun _ τ => Prefix (encodeVector (fun i => (integerNormal a i : ℚ))) "lp.word" τ ∧
        τ.vars "lp.position"=3*n ∧ τ.vars "projection.n"=n)
      (145*n+28) := by
  have hlen : (encodeVector a).length=3*n := by
    change (RamVectorEncoding.encode (List.ofFn a)).length=_
    rw [RamVectorEncoding.length_encode,List.length_ofFn]
  have hsetup : Spec B (fun σ => σ.vars "projection.n"=n) setup
      (fun _ τ => τ.vars "slice.start"=0 ∧ τ.vars "fill.length"=3*n) 6 := by
    intro σ hh
    run_vcg
    all_goals simp_all
  rintro σ ⟨hp,hN,hS,hO⟩
  obtain ⟨ν,r1,p1⟩ := hsetup σ hN
  have hpν : Prefix (encodeVector a) "lp.word" ν := by
    simpa only [Prefix,r1.frame_arr "lp.word" (by decide)] using hp
  obtain ⟨μ,r2,p2⟩ := NativeSlice.command_spec B "lp.word" "cut.source" [] (encodeVector a) [] (by decide)
    (by rw [List.length_nil,hlen]; omega)
    (NativeRationalBounds.vector_words B M n a (by omega) (by omega) ha) ν
    ⟨⟨by simpa using hpν,by simpa using p1.1⟩,by simpa only [hlen] using p1.2,
      by rw [hlen,RamFrames.run_array_length r1]; exact hS⟩
  have hc : NativeCutRead.Context a μ :=
    ⟨p2.2,((r1.seq r2).frame_var "projection.n" (by decide)).trans hN⟩
  obtain ⟨ξ,r3,p3⟩ := NativeDenominatorProduct.command_spec B M n a (by omega) (by omega) (by omega) ha μ hc
  obtain ⟨τ,r4,p4⟩ := NativeCutVector.command_spec B M n a hB ha ξ
    ⟨p3,by rwa [RamFrames.run_array_length (r1.seq (r2.seq r3))]⟩
  exact ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono (by rw [hlen]; omega),p4.2.1,p4.2.2,p4.1.1.2⟩

end Lax263307Proofs.NativeClearNormal
