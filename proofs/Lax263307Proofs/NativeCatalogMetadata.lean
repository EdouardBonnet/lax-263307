import Lax263307.IndependentSetEncoding
import Lax263307Proofs.NativeTabulate
import Lax263307Proofs.NativeMaskUnpack

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeCatalogMetadata

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307.WeightedIndependentSet
open Lax263307

abbrev N (n r : ℕ) := (CoordinateCatalog.catalog n r).length

def atIndex (n r : ℕ) (j : Fin (N n r)) : Finset (Fin n) := (CoordinateCatalog.indexing n r j).val

def cards (n r : ℕ) : List ℕ := List.ofFn fun j : Fin (N n r) => (atIndex n r j).card

def independent {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : ℕ) : List ℕ :=
  List.ofFn fun j : Fin (N n r) => if G.IsIndepSet (atIndex n r j : Set (Fin n)) then 1 else 0

def Data {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : ℕ) (σ : Env) : Prop :=
  σ.vars "graph.n"=n ∧ σ.vars "catalog.count"=N n r ∧
  Prefix (Lax263307.NativeCatalog.words n r) "catalog.mask" σ ∧
  Prefix (NativeWeightReduction.adjacency G) "search.graph" σ ∧ n≤(σ.arrs "subset.bits").length

theorem data_frame {n B K : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : ℕ)
    {c : Com} {σ τ : Env} (rr : Run B c σ τ K)
    (h0 : "graph.n"∉c.wvars) (h1 : "catalog.count"∉c.wvars)
    (h2 : "catalog.mask"∉c.warrs) (h3 : "search.graph"∉c.warrs) (hσ : Data G r σ) : Data G r τ := by
  rcases hσ with ⟨hn,hc,hm,hg,hr⟩
  refine ⟨(rr.frame_var "graph.n" h0).trans hn,(rr.frame_var "catalog.count" h1).trans hc,?_,?_,?_⟩
  · simpa only [Prefix,rr.frame_arr "catalog.mask" h2] using hm
  · simpa only [Prefix,rr.frame_arr "search.graph" h3] using hg
  · rwa [Lax455465Proofs.RamFrames.run_array_length rr]

def readMask : Com := .assign "unpack.mask" (.get "catalog.mask" (.var "fill.i"))

theorem read_mask_spec {n : ℕ} (B : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : ℕ)
    (i : Fin (N n r)) (hN : N n r<B) (hm : 2^n<B) :
    Spec B (fun σ => Data G r σ ∧ σ.vars "fill.i"=i.val) readMask
      (fun _ τ => Data G r τ ∧ τ.vars "unpack.mask"=NativeMasks.mask (atIndex n r i)) 3 := by
  rintro σ ⟨hd,hi⟩
  have hlen : (Lax263307.NativeCatalog.words n r).length=N n r := by simp [Lax263307.NativeCatalog.words]
  have hget := hd.2.2.1 i.val (by rw [hlen]; exact i.isLt)
  have hw : (Lax263307.NativeCatalog.words n r)[i.val]=NativeMasks.mask (atIndex n r i) := by
    simp only [Lax263307.NativeCatalog.words,List.getElem_map]
    rfl
  rw [hw] at hget
  let τ := σ.setVar "unpack.mask" (NativeMasks.mask (atIndex n r i))
  have rr : Run B readMask σ τ 3 := Run.assign
    (evalB_get (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ i.isLt.trans hN⟩)
      hget ((NativeMasks.mask_bound _).trans hm))
  exact ⟨τ,rr,data_frame G r rr (by decide) (by decide) (by decide) (by decide) hd,by simp [τ]⟩

def prepareSet : Com := .seq readMask NativeMaskUnpack.command

theorem prepare_set_spec {n : ℕ} (B : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : ℕ)
    (i : Fin (N n r)) (hB : n+2<B) (hN : N n r<B) (hm : 2^n<B) :
    Spec B (fun σ => Data G r σ ∧ σ.vars "fill.i"=i.val) prepareSet
      (fun _ τ => Data G r τ ∧ Prefix (encodeOutput (atIndex n r i)) "subset.bits" τ ∧
        τ.vars "unpack.card"=(atIndex n r i).card) (21*n+11) := by
  rintro σ ⟨hd,hi⟩
  obtain ⟨ν,r1,p1⟩ := read_mask_spec B G r i hN hm σ ⟨hd,hi⟩
  obtain ⟨τ,r2,p2⟩ := NativeMaskUnpack.command_spec B (atIndex n r i) hB hm ν
    ⟨p1.1.1,p1.2,p1.1.2.2.2.2⟩
  exact ⟨τ,(r1.seq r2).mono (by omega),
    data_frame G r r2 (by decide) (by decide) (by decide) (by decide) p1.1,p2⟩

def readCard : Com := .seq prepareSet (.assign "fill.value" (.var "unpack.card"))

theorem read_card_spec {n : ℕ} (B : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : ℕ)
    (i : Fin (N n r)) (hB : n+2<B) (hN : N n r<B) (hm : 2^n<B) :
    Spec B (fun σ => Data G r σ ∧ σ.vars "fill.i"=i.val) readCard
      (fun _ τ => Data G r τ ∧ τ.vars "fill.value"=(atIndex n r i).card) (21*n+13) := by
  rintro σ ⟨hd,hi⟩
  obtain ⟨ν,r1,p1⟩ := prepare_set_spec B G r i hB hN hm σ ⟨hd,hi⟩
  let τ := ν.setVar "fill.value" (atIndex n r i).card
  have r2 : Run B (.assign "fill.value" (.var "unpack.card")) ν τ 2 := Run.assign
    (by rw [evalB_var_iff]; exact ⟨p1.2.2.symm,p1.2.2 ▸ (NativeMaskUnpack.card_bound _).trans_lt (by omega)⟩)
  exact ⟨τ,(r1.seq r2).mono (by omega),
    data_frame G r r2 (by decide) (by decide) (by decide) (by decide) p1.1,by simp [τ]⟩

def readIndependent : Com := .seq prepareSet
  (.seq (NativeIndependentTest.command "search.graph" "subset.bits") (.assign "fill.value" (.var "test.ok")))

theorem read_independent_spec {n : ℕ} (B : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : ℕ)
    (i : Fin (N n r)) (hB : n*n+n+3<B) (hN : N n r<B) (hm : 2^n<B) :
    Spec B (fun σ => Data G r σ ∧ σ.vars "fill.i"=i.val) readIndependent
      (fun _ τ => Data G r τ ∧ τ.vars "fill.value"=if G.IsIndepSet (atIndex n r i : Set (Fin n)) then 1 else 0)
      (38*n*n+21*n+25) := by
  rintro σ ⟨hd,hi⟩
  obtain ⟨ν,r1,p1⟩ := prepare_set_spec B G r i (by omega) hN hm σ ⟨hd,hi⟩
  obtain ⟨μ,r2,p2⟩ := NativeIndependentTest.command_spec B G (atIndex n r i) "search.graph" "subset.bits" hB ν
    ⟨p1.1.1,p1.1.2.2.2.1,p1.2.1⟩
  have hok : μ.vars "test.ok"=if G.IsIndepSet (atIndex n r i : Set (Fin n)) then 1 else 0 := by
    split_ifs with h
    · exact p2.2.2.mpr h
    · have hh : μ.vars "test.ok"≠1 := fun h1 => h (p2.2.2.mp h1)
      omega
  let τ := μ.setVar "fill.value" (μ.vars "test.ok")
  have r3 : Run B (.assign "fill.value" (.var "test.ok")) μ τ 2 := Run.assign (evalB_var (p2.2.1.trans_lt (by omega)))
  have rr := r1.seq (r2.seq r3)
  exact ⟨τ,rr.mono (by omega),data_frame G r rr (by decide) (by decide) (by decide) (by decide) hd,
    by simpa only [τ,vars_setVar,if_true] using hok⟩

def command : Com := .seq (.assign "fill.length" (.var "catalog.count"))
  (.seq (NativeTabulate.command "catalog.card" readCard) (NativeTabulate.command "catalog.independent" readIndependent))

theorem command_spec {n : ℕ} (B : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : ℕ)
    (hB : n*n+n+3<B) (hN : N n r+1<B) (hm : 2^n<B) :
    Spec B (fun σ => Data G r σ ∧ N n r≤(σ.arrs "catalog.card").length ∧ N n r≤(σ.arrs "catalog.independent").length)
      command (fun _ τ => Data G r τ ∧ Prefix (cards n r) "catalog.card" τ ∧ Prefix (independent G r) "catalog.independent" τ)
      ((38*n*n+42*n+60)*(N n r)+14) := by
  have hc : (cards n r).length=N n r := List.length_ofFn
  have hi : (independent G r).length=N n r := List.length_ofFn
  have hcards := NativeTabulate.command_spec B (cards n r) "catalog.card" (Data G r) readCard (21*n+13)
    (by rwa [hc]) (by intro z hz; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hz; exact (NativeMaskUnpack.card_bound _).trans_lt (by omega))
    (by decide) (by decide) (by decide)
    (by intro σ h; simpa [Data,Prefix] using h)
    (by intro σ τ rr h; exact data_frame G r rr (by decide) (by decide) (by decide) (by decide) h)
    (by intro i hi; simpa only [cards,List.getElem_ofFn] using read_card_spec B G r ⟨i,by rwa [hc] at hi⟩ (by omega) (by omega) hm)
  have hind := NativeTabulate.command_spec B (independent G r) "catalog.independent" (Data G r) readIndependent (38*n*n+21*n+25)
    (by rwa [hi]) (by intro z hz; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hz; split_ifs <;> omega)
    (by decide) (by decide) (by decide)
    (by intro σ h; simpa [Data,Prefix] using h)
    (by intro σ τ rr h; exact data_frame G r rr (by decide) (by decide) (by decide) (by decide) h)
    (by intro i h; simpa only [independent,List.getElem_ofFn] using read_independent_spec B G r ⟨i,by rwa [hi] at h⟩ hB (by omega) hm)
  rintro σ ⟨hd,hcr,hir⟩
  let ν := σ.setVar "fill.length" (N n r)
  have r1 : Run B (.assign "fill.length" (.var "catalog.count")) σ ν 2 := Run.assign
    (by rw [evalB_var_iff]; exact ⟨hd.2.1.symm,hd.2.1 ▸ (by omega)⟩)
  have d1 := data_frame G r r1 (by decide) (by decide) (by decide) (by decide) hd
  obtain ⟨μ,r2,p2⟩ := hcards ν ⟨d1,by simp [ν,hc],by simpa only [ν,arrs_setVar,hc] using hcr⟩
  have hlength : μ.vars "fill.length"=(independent G r).length := by
    rw [r2.frame_var "fill.length" (by decide)]
    simp [ν,hi]
  obtain ⟨τ,r3,p3⟩ := hind μ ⟨p2.1,hlength,by rw [hi,Lax455465Proofs.RamFrames.run_array_length r2]; exact hir⟩
  refine ⟨τ,(r1.seq (r2.seq r3)).mono (by rw [hc,hi]; nlinarith),p3.1,?_,p3.2⟩
  simpa only [Prefix,r3.frame_arr "catalog.card" (by decide)] using p2.2

end Lax263307Proofs.NativeCatalogMetadata
