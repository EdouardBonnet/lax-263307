import Lax263307Proofs.NativeSelectedVertices
import Lax263307Proofs.NativeLargeCapacity
import Lax263307Proofs.NativeRestrictionRead

namespace Lax263307Proofs.NativeFlowPrepare

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 NativeSignedArithmetic
open Lax109476.RationalEncoding

def command : Com := .seq (.assign "unpack.mask" (.var "separator.remaining"))
  (.seq NativeMaskUnpack.command (.seq NativeSelectedVertices.command NativeLargeCapacity.command))

/-- Build the increasing induced-vertex table and the exact finite
capacity from the remaining-set mask and the algorithm's parameters. -/
theorem command_spec (B b n load k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ) (R : Finset (Fin n)) (hn : 0<n) (hl : 0<load)
    (hB : n+2<B) (hm : 2^n<B) (hlarge : NativeLargeCapacity.resource b n R.card load k<B) :
    Spec B (fun σ => Prefix (NativeWeightReduction.adjacency G) "search.graph" σ ∧
      Prefix (encodeVector x) "near.costs" σ ∧ σ.vars "graph.n"=n ∧
      σ.vars "separator.remaining"=NativeMasks.mask R ∧ σ.vars "class.B"=b ∧
      σ.vars "algorithm.load"=load ∧ σ.vars "conditioning.k"=k ∧
      n≤(σ.arrs "subset.bits").length ∧ n≤(σ.arrs "restrict.vertices").length)
      command (fun _ τ => NativeRestrictionRead.Data G x R τ ∧
        Stored "split.large" (ComputedSeparators.largeCapacity b n R.card load k : ℚ) τ)
      (43*n+12*(2*n).size+78) := by
  rintro σ ⟨hg,hx,hnσ,hR,hb,hlσ,hk,hbits,hvertices⟩
  let σ1 := σ.setVar "unpack.mask" (NativeMasks.mask R)
  have r1 : Run B (.assign "unpack.mask" (.var "separator.remaining")) σ σ1 2 := Run.assign
    (by rw [evalB_var_iff]; exact ⟨hR.symm,hR ▸ (NativeMasks.mask_bound R).trans hm⟩)
  obtain ⟨σ2,r2,p2⟩ := NativeMaskUnpack.command_spec B R hB hm σ1
    ⟨by simpa [σ1] using hnσ,by simp [σ1],hbits⟩
  have r12 := r1.seq r2
  obtain ⟨σ3,r3,p3⟩ := NativeSelectedVertices.command_spec B n R hB σ2
    ⟨(r12.frame_var "graph.n" (by decide)).trans hnσ,p2.1,
      by rwa [RamFrames.run_array_length r12]⟩
  have r123 := r1.seq (r2.seq r3)
  obtain ⟨τ,r4,p4⟩ := NativeLargeCapacity.command_spec B b n R.card load k hn hl hlarge σ3
    ⟨(r123.frame_var "class.B" (by decide)).trans hb,p3.1.1,p3.2.2,
      (r123.frame_var "algorithm.load" (by decide)).trans hlσ,
      (r123.frame_var "conditioning.k" (by decide)).trans hk⟩
  have rr := r1.seq (r2.seq (r3.seq r4))
  refine ⟨τ,rr.mono (by omega),⟨?_,?_,?_,?_,?_⟩,p4⟩
  · simpa only [Prefix,r4.frame_arr "restrict.vertices" (by decide)] using p3.2.1
  · simpa only [Prefix,rr.frame_arr "search.graph" (by decide)] using hg
  · simpa only [Prefix,rr.frame_arr "near.costs" (by decide)] using hx
  · exact (r4.frame_var "restrict.count" (by decide)).trans p3.2.2
  · exact (rr.frame_var "graph.n" (by decide)).trans hnσ

end Lax263307Proofs.NativeFlowPrepare
