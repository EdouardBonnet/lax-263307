import Lax263307Proofs.NativeCatalogMetadata
import Lax263307Proofs.NativeMomentRows

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeMomentAccess

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307 NativeCatalogMetadata

def Data {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : ℕ) (σ : Env) : Prop :=
  NativeCatalogMetadata.Data G r σ ∧ Prefix (cards n r) "catalog.card" σ ∧
  Prefix (independent G r) "catalog.independent" σ ∧ σ.vars "moment.r"=r

def load : Com := .seq (.assign "row.mask" (.get "catalog.mask" (.var "row.index")))
  (.seq (.assign "row.card" (.get "catalog.card" (.var "row.index")))
    (.seq (.assign "row.independent" (.get "catalog.independent" (.var "row.index")))
      (.assign "column.mask" (.get "catalog.mask" (.var "column.index")))))

def activate : Com := .ite (.lt (.var "row.card") (.add (.var "moment.r") (.lit 2)))
  (.assign "row.active" (.lit 1)) (.assign "row.active" (.lit 0))

theorem activate_spec (B c r : ℕ) (hB : c+r+3<B) :
    Spec B (fun σ => σ.vars "row.card"=c ∧ σ.vars "moment.r"=r) activate
      (fun _ τ => τ.vars "row.active"=if c≤r+1 then 1 else 0) 8 := by
  by_cases h : c<r+2
  · have h' : c≤r+1 := by omega
    run_vcg
    all_goals simp_all [Env.setVar]
  · have h' : ¬c≤r+1 := by omega
    run_vcg
    all_goals simp_all [Env.setVar]
    all_goals omega

def Loaded {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : ℕ)
    (i j : Fin (N n r)) (σ : Env) : Prop :=
  σ.vars "row.mask"=NativeMasks.mask (atIndex n r i) ∧
  σ.vars "column.mask"=NativeMasks.mask (atIndex n r j) ∧
  σ.vars "row.card"=(atIndex n r i).card ∧
  σ.vars "row.independent"=(if G.IsIndepSet (atIndex n r i : Set (Fin n)) then 1 else 0)

theorem mask_word (n r : ℕ) (i : Fin (N n r)) :
    (Lax263307.NativeCatalog.words n r)[i.val]?=some (NativeMasks.mask (atIndex n r i)) := by
  rw [Lax263307.NativeCatalog.words,List.getElem?_map,List.getElem?_eq_getElem i.isLt]
  rfl

theorem load_spec {n : ℕ} (B : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : ℕ)
    (i j : Fin (N n r)) (hB : n+r+3<B) (hN : N n r<B) (hm : 2^n<B) :
    Spec B (fun σ => Data G r σ ∧ σ.vars "row.index"=i.val ∧ σ.vars "column.index"=j.val)
      load (fun _ τ => Loaded G r i j τ) 12 := by
  rintro σ ⟨hd,hi,hj⟩
  have hlen : (Lax263307.NativeCatalog.words n r).length=N n r := by simp [Lax263307.NativeCatalog.words]
  have hmask : ∀ l : Fin (N n r),(σ.arrs "catalog.mask")[l.val]?=some (NativeMasks.mask (atIndex n r l)) := by
    intro l
    have hli : l.val<(Lax263307.NativeCatalog.words n r).length := by rw [hlen]; exact l.isLt
    have hh := hd.1.2.2.1 l.val hli
    have he := mask_word n r l
    rw [List.getElem?_eq_getElem hli] at he
    exact hh.trans he
  have hcard : (σ.arrs "catalog.card")[i.val]?=some (atIndex n r i).card := by
    have hh := hd.2.1 i.val (by simp [cards])
    simpa only [cards,List.getElem_ofFn] using hh
  have hind : (σ.arrs "catalog.independent")[i.val]?=
      some (if G.IsIndepSet (atIndex n r i : Set (Fin n)) then 1 else 0) := by
    have hh := hd.2.2.1 i.val (by simp [independent])
    simpa only [independent,List.getElem_ofFn] using hh
  have hcardB : (atIndex n r i).card<B := (NativeMaskUnpack.card_bound _).trans_lt (by omega)
  have hindB : (if G.IsIndepSet (atIndex n r i : Set (Fin n)) then 1 else 0)<B := by split_ifs <;> omega
  have hiB := i.isLt.trans hN
  have hjB := j.isLt.trans hN
  have hrowB := (NativeMasks.mask_bound (atIndex n r i)).trans hm
  have hcolB := (NativeMasks.mask_bound (atIndex n r j)).trans hm
  let ν := σ.setVar "row.mask" (NativeMasks.mask (atIndex n r i))
  have r1 : Run B (.assign "row.mask" (.get "catalog.mask" (.var "row.index"))) σ ν 3 :=
    Run.assign (evalB_get (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ hiB⟩) (hmask i) hrowB)
  have hiν : ν.vars "row.index"=i.val := (r1.frame_var "row.index" (by decide)).trans hi
  let μ := ν.setVar "row.card" (atIndex n r i).card
  have r2 : Run B (.assign "row.card" (.get "catalog.card" (.var "row.index"))) ν μ 3 :=
    Run.assign (evalB_get (by rw [evalB_var_iff]; exact ⟨hiν.symm,hiν ▸ hiB⟩) hcard hcardB)
  have hiμ : μ.vars "row.index"=i.val := (r2.frame_var "row.index" (by decide)).trans hiν
  let ξ := μ.setVar "row.independent" (if G.IsIndepSet (atIndex n r i : Set (Fin n)) then 1 else 0)
  have r3 : Run B (.assign "row.independent" (.get "catalog.independent" (.var "row.index"))) μ ξ 3 :=
    Run.assign (evalB_get (by rw [evalB_var_iff]; exact ⟨hiμ.symm,hiμ ▸ hiB⟩) hind hindB)
  have hjξ : ξ.vars "column.index"=j.val := ((r1.seq (r2.seq r3)).frame_var "column.index" (by decide)).trans hj
  let τ := ξ.setVar "column.mask" (NativeMasks.mask (atIndex n r j))
  have r4 : Run B (.assign "column.mask" (.get "catalog.mask" (.var "column.index"))) ξ τ 3 :=
    Run.assign (evalB_get (by rw [evalB_var_iff]; exact ⟨hjξ.symm,hjξ ▸ hjB⟩) (hmask j) hcolB)
  have rr := r1.seq (r2.seq (r3.seq r4))
  refine ⟨τ,rr,?_,?_,?_,?_⟩
  · rw [(r2.seq (r3.seq r4)).frame_var "row.mask" (by decide)]
    exact (vars_setVar σ "row.mask" (NativeMasks.mask (atIndex n r i)) "row.mask").trans (if_pos rfl)
  · exact (vars_setVar ξ "column.mask" (NativeMasks.mask (atIndex n r j)) "column.mask").trans (if_pos rfl)
  · rw [(r3.seq r4).frame_var "row.card" (by decide)]
    exact (vars_setVar ν "row.card" (atIndex n r i).card "row.card").trans (if_pos rfl)
  · rw [r4.frame_var "row.independent" (by decide)]
    exact (vars_setVar μ "row.independent" _ "row.independent").trans (if_pos rfl)

def command : Com := .seq load activate

theorem command_spec {n : ℕ} (B : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : ℕ)
    (i j : Fin (N n r)) (hB : n+r+3<B) (hN : N n r<B) (hm : 2^n<B) :
    Spec B (fun σ => Data G r σ ∧ σ.vars "row.index"=i.val ∧ σ.vars "column.index"=j.val)
      command (fun _ τ => Loaded G r i j τ ∧ τ.vars "row.active"=if (atIndex n r i).card≤r+1 then 1 else 0) 20 := by
  rintro σ ⟨hd,hi,hj⟩
  obtain ⟨ν,r1,p1⟩ := load_spec B G r i j hB hN hm σ ⟨hd,hi,hj⟩
  obtain ⟨τ,r2,p2⟩ := activate_spec B (atIndex n r i).card r
    (by have h := NativeMaskUnpack.card_bound (atIndex n r i); omega) ν
    ⟨p1.2.2.1,(r1.frame_var "moment.r" (by decide)).trans hd.2.2.2⟩
  refine ⟨τ,r1.seq r2,?_,p2⟩
  simpa only [Loaded,r2.frame_var "row.mask" (by decide),r2.frame_var "column.mask" (by decide),
    r2.frame_var "row.card" (by decide),r2.frame_var "row.independent" (by decide)] using p1

end Lax263307Proofs.NativeMomentAccess
