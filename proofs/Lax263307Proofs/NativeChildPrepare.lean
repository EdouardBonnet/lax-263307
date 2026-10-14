import Lax263307Proofs.NativeChildGraph
import Lax263307Proofs.NativeSelectedVertices

namespace Lax263307Proofs.NativeChildPrepare

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators NativeMasks

def command : Com := .seq NativeMaskUnpack.command
  (.seq NativeSelectedVertices.command NativeChildGraph.command)

/-- Build a child graph from its subset mask using actual bit decoding,
canonical label construction, and induced adjacency computation. -/
theorem command_spec (B n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ) (R : Finset (Fin n)) (hB : n*n+n+3<B) (hm : 2^n<B) :
    Spec B (fun σ => Prefix (NativeWeightReduction.adjacency G) "search.graph" σ ∧
      Prefix (Lax109476.RationalEncoding.encodeVector x) "near.costs" σ ∧
      σ.vars "graph.n"=n ∧ σ.vars "unpack.mask"=mask R ∧
      n≤(σ.arrs "subset.bits").length ∧ n≤(σ.arrs "restrict.vertices").length ∧
      R.card*R.card≤(σ.arrs "child.graph").length) command
      (fun _ τ => NativeRestrictionRead.Data G x R τ ∧
        Prefix (NativeWeightReduction.adjacency (restriction G R)) "child.graph" τ)
      (43*n+36*(R.card*R.card)+26) := by
  rintro σ ⟨hg,hx,hn,hr,hbits,hlabels,hchild⟩
  obtain ⟨ν,r1,p1⟩ := NativeMaskUnpack.command_spec B R (by omega) hm σ ⟨hn,hr,hbits⟩
  have hn1 := (r1.frame_var "graph.n" (by decide)).trans hn
  obtain ⟨μ,r2,p2⟩ := NativeSelectedVertices.command_spec B n R (by omega) ν
    ⟨hn1,p1.1,by rwa [RamFrames.run_array_length r1]⟩
  have rr := r1.seq r2
  have hd : NativeRestrictionRead.Data G x R μ :=
    ⟨p2.2.1,by simpa only [Prefix,rr.frame_arr "search.graph" (by decide)] using hg,
      by simpa only [Prefix,rr.frame_arr "near.costs" (by decide)] using hx,p2.2.2,p2.1.1⟩
  obtain ⟨τ,r3,p3⟩ := NativeChildGraph.command_spec B n G x R hB μ
    ⟨hd,by rwa [RamFrames.run_array_length rr]⟩
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),p3⟩

end Lax263307Proofs.NativeChildPrepare
