import Lax263307Proofs.NativeSlice
import Lax263307Proofs.NativeCertificateRead

namespace Lax263307Proofs.NativeProjectionNear

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.RationalEncoding
open Lax263307.DistanceProjection

theorem encode_point_distance {n : ℕ} (z : Fin (n+1) → ℚ) :
    encodeVector z=encodeVector (point z)++encodeRational (distance z) := by
  unfold encodeVector
  rw [List.ofFn_add,List.flatMap_append]
  simp [distance,List.ofFn_succ]
  apply congrArg (fun f : Fin n → ℚ => (List.ofFn f).flatMap encodeRational)
  funext i
  change z (Fin.castLE _ i)=z (Fin.castAdd 1 i)
  congr 1

def setup : Com := .seq (.assign "slice.start" (.lit 1))
  (.seq (.assign "fill.length" (.mul (.lit 3) (.var "projection.n")))
    (.assign "lp.position" (.var "fill.length")))

def command : Com := .seq setup (NativeSlice.command "vm.output" "lp.word")

/-- Extract the primal point from an optimal distance certificate; the
last primal coordinate is the distance and is deliberately left behind. -/
theorem command_spec (B m n : ℕ) (z : Fin (n+1) → ℚ) (y : Fin (m+(n+n)) → ℚ)
    (hs : 3*n+10<B) (hwords : ∀ v∈encodeVector (point z),v<B) :
    Spec B (fun σ => Prefix (encodeCertificate (.optimal z y)) "vm.output" σ ∧
      σ.vars "projection.n"=n ∧ 3*n≤(σ.arrs "lp.word").length) command
      (fun _ τ => Prefix (encodeVector (point z)) "lp.word" τ ∧ τ.vars "lp.position"=3*n)
      (48*n+14) := by
  have hlen : (encodeVector (point z)).length=3*n := by
    change (RamVectorEncoding.encode (List.ofFn (point z))).length=_
    rw [RamVectorEncoding.length_encode,List.length_ofFn]
  have hsetup : Spec B (fun σ => σ.vars "projection.n"=n) setup
      (fun _ τ => τ.vars "slice.start"=1 ∧ τ.vars "fill.length"=3*n ∧ τ.vars "lp.position"=3*n) 8 := by
    intro σ hh
    run_vcg
    all_goals simp_all
  rintro σ ⟨hc,hN,hr⟩
  obtain ⟨ν,r1,p1⟩ := hsetup σ hN
  have hp : Prefix ([0]++(encodeVector (point z)++(encodeRational (distance z)++encodeVector y))) "vm.output" ν := by
    simpa only [Prefix,r1.frame_arr "vm.output" (by decide),encodeCertificate,encode_point_distance,List.append_assoc] using hc
  obtain ⟨τ,r2,p2⟩ := NativeSlice.command_spec B "vm.output" "lp.word" [0]
    (encodeVector (point z)) (encodeRational (distance z)++encodeVector y) (by decide)
    (by simp only [List.length_cons,List.length_nil,hlen]; omega) hwords ν
    ⟨⟨hp,by simpa using p1.1⟩,by simpa only [hlen] using p1.2.1,
      by rw [hlen,RamFrames.run_array_length r1]; exact hr⟩
  exact ⟨τ,(r1.seq r2).mono (by rw [hlen]; omega),p2.2,
    (r2.frame_var "lp.position" (by decide)).trans p1.2.2⟩

end Lax263307Proofs.NativeProjectionNear
