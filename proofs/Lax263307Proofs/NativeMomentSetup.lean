import Lax263307Proofs.NativeMomentInput

set_option maxHeartbeats 200000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeMomentSetup

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307 MomentLP

abbrev N (n r : ℕ) := dimension n r

def guardBound (n k r : ℕ) : ℕ :=
  n*n+(n+1)*(r+3)+NativeMomentInput.length n r+n+k+r+N n r+20

def Input {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ) (σ : Env) : Prop :=
  σ.vars "graph.n"=n ∧ σ.vars "row.k"=k ∧ σ.vars "moment.r"=r ∧
  Prefix (NativeWeightReduction.adjacency G) "search.graph" σ ∧
  (n+1)*(r+3) ≤ (σ.arrs "choose.table").length ∧ n ≤ (σ.arrs "subset.bits").length ∧
  N n r ≤ (σ.arrs "catalog.mask").length ∧ N n r ≤ (σ.arrs "catalog.card").length ∧
  N n r ≤ (σ.arrs "catalog.independent").length

def catalogCost (n r : ℕ) : ℕ :=
  (54*(n+1)*(r+3)+(69*n+33)*N n r+41)*(r+3)+8

def cost (n r : ℕ) : ℕ := catalogCost n r+(38*n*n+42*n+60)*N n r+18

def command : Com := .seq (.assign "catalog.limit" (.add (.var "moment.r") (.lit 3)))
  (.seq NativeCatalog.command NativeCatalogMetadata.command)

theorem catalog_length (n r : ℕ) : (NativeCatalog.rows n (r+3)).length=N n r := by
  rw [NativeCatalog.rows_words]
  simp only [Lax263307.NativeCatalog.words,List.length_map]

theorem command_spec {n : ℕ} (B : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ)
    (hB : guardBound n k r < B) (hm : 2^n < B) :
    Spec B (Input G k r) command (fun _ τ => NativeMomentFamily.Data G k r τ) (cost n r) := by
  have hb : n*n+(n+1)*(r+3)+NativeMomentInput.length n r+n+k+r+N n r+20 < B := hB
  rintro σ ⟨hn,hk,hr,hg,htable,hbits,hmask,hcard,hind⟩
  let ν := σ.setVar "catalog.limit" (r+3)
  have r1 : Run B (.assign "catalog.limit" (.add (.var "moment.r") (.lit 3))) σ ν 4 := Run.assign
    (evalB_bin (op := .add) (by rw [evalB_var_iff]; exact ⟨hr.symm,hr ▸ (by omega)⟩)
      (evalB_lit (show 3 < B by omega)) (by change r+3 < B; omega))
  have hcoeff : ∀ a ≤ n,∀ b ≤ r+2,a.choose b < B := by
    intro a ha b hb'
    have hh := NativeCatalog.coefficient_bound n (r+2) a b ha hb'
    rw [show r+2+1=r+3 from rfl,catalog_length] at hh
    omega
  obtain ⟨μ,r2,p2⟩ := NativeCatalog.command_spec B n (r+2) (by change (n+1)*(r+3)+n+(r+2)+3 < B; omega) hm
    (by rw [show r+2+1=r+3 from rfl,catalog_length]; omega) hcoeff ν
    ⟨(r1.frame_var "graph.n" (by decide)).trans hn,by simp [ν],htable,hbits,by rwa [catalog_length]⟩
  have hd : NativeCatalogMetadata.Data G r μ := by
    refine ⟨p2.1.1,?_,?_,?_,?_⟩
    · simpa only [show r+2+1=r+3 from rfl,catalog_length] using p2.2.1
    · simpa only [show r+2+1=r+3 from rfl,NativeCatalog.rows_words] using p2.2.2
    · simpa only [Prefix,(r1.seq r2).frame_arr "search.graph" (by decide)] using hg
    · rwa [Lax455465Proofs.RamFrames.run_array_length (r1.seq r2)]
  obtain ⟨τ,r3,p3⟩ := NativeCatalogMetadata.command_spec B G r (by omega)
    (by change N n r+1 < B; omega) hm μ
    ⟨hd,by rwa [Lax455465Proofs.RamFrames.run_array_length (r1.seq r2)],
      by rwa [Lax455465Proofs.RamFrames.run_array_length (r1.seq r2)]⟩
  have rr := r1.seq (r2.seq r3)
  refine ⟨τ,rr.mono ?_,⟨p3.1,p3.2.1,p3.2.2,?_⟩,?_⟩
  · simp only [show r+2+1=r+3 from rfl,catalog_length,cost,catalogCost,NativeCatalogMetadata.N,N,MomentLP.dimension]
    omega
  · exact (rr.frame_var "moment.r" (by decide)).trans hr
  · exact (rr.frame_var "row.k" (by decide)).trans hk

end Lax263307Proofs.NativeMomentSetup
