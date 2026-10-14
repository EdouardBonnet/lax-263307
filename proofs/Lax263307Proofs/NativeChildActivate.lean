import Lax263307Proofs.NativeSlice
import Lax263307Proofs.NativeWeightReduction

namespace Lax263307Proofs.NativeChildActivate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

def setup : Com := .seq (.assign "fill.length" (.mul (.var "restrict.count") (.var "restrict.count")))
  (.assign "slice.start" (.lit 0))

def command : Com := .seq setup (.seq (NativeSlice.command "child.graph" "search.graph")
  (.assign "graph.n" (.var "restrict.count")))

theorem setup_spec (B r : ℕ) (hB : r*r+r+3<B) :
    Spec B (fun σ => σ.vars "restrict.count"=r) setup
      (fun _ τ => τ.vars "fill.length"=r*r ∧ τ.vars "slice.start"=0 ∧ τ.vars "restrict.count"=r) 6 := by
  intro σ hs
  run_vcg
  all_goals simp_all [Env.setVar] <;> omega

/-- Activate a prepared child graph. Parent data can be restored from
the recursion frame after the child returns. -/
theorem command_spec (B r : ℕ) (G : SimpleGraph (Fin r)) [DecidableRel G.Adj] (hB : r*r+r+3<B) :
    Spec B (fun σ => Prefix (NativeWeightReduction.adjacency G) "child.graph" σ ∧
      σ.vars "restrict.count"=r ∧ r*r≤(σ.arrs "search.graph").length) command
      (fun _ τ => Prefix (NativeWeightReduction.adjacency G) "search.graph" τ ∧ τ.vars "graph.n"=r)
      (16*(r*r)+14) := by
  let xs := NativeWeightReduction.adjacency G
  have hlen : xs.length=r*r := NativeWeightReduction.adjacency_length G
  have hwords : ∀ z∈xs,z<B := by
    intro z hz
    obtain ⟨row,hrow,hz⟩ := List.mem_flatten.mp hz
    obtain ⟨u,rfl⟩ := List.mem_ofFn.mp hrow
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hz
    split_ifs <;> omega
  rintro σ ⟨hg,hr,hroom⟩
  obtain ⟨ν,r1,p1⟩ := setup_spec B r hB σ hr
  obtain ⟨μ,r2,p2⟩ := NativeSlice.command_spec B "child.graph" "search.graph" [] xs [] (by decide)
    (by simp [hlen]; omega) hwords ν
    ⟨⟨by simpa only [List.nil_append,List.append_nil,Prefix,r1.frame_arr "child.graph" (by decide)] using hg,
      by simpa only [List.length_nil] using p1.2.1⟩,
      by simpa only [hlen] using p1.1,by simpa only [hlen,RamFrames.run_array_length r1] using hroom⟩
  have hr2 := (r2.frame_var "restrict.count" (by decide)).trans p1.2.2
  let τ := μ.setVar "graph.n" r
  have r3 : Run B (.assign "graph.n" (.var "restrict.count")) μ τ 2 := Run.assign
    (by rw [evalB_var_iff]; exact ⟨hr2.symm,hr2 ▸ (by omega : r<B)⟩)
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by rw [hlen]; omega),
    by simpa only [Prefix,τ,arrs_setVar] using p2.2,by simp [τ]⟩

end Lax263307Proofs.NativeChildActivate
