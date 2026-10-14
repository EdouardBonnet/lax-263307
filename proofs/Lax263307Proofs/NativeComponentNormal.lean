import Lax263307Proofs.NativeComponentCoefficient
import Lax263307Proofs.NativeRationalTabulate
import Lax263307Proofs.NativeProgramCache
import Lax263307Proofs.NativeArrayBounds
import Lax263307Proofs.NativeRoundedQuery
import Lax263307.ProjectedOracle

set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeComponentNormal

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 NativeMasks NativeCatalogMetadata

def normal {n r : ℕ} (A C : Finset (Fin n)) (u : ℕ) : MomentLP.Index n r → ℤ :=
  MomentLP.encode (ComponentCutEncoding.coefficient A C u)

def values {n : ℕ} (r : ℕ) (A C : Finset (Fin n)) (u : ℕ) : List ℚ :=
  List.ofFn (RoundedOracleSearch.rationalNormal (normal (r:=r) A C u))

theorem cleared_integer {N : ℕ} (a : Fin N → ℤ) :
    RationalCutBuffer.integerNormal (RoundedOracleSearch.rationalNormal a)=a := by
  funext i
  simp [RationalCutBuffer.integerNormal,RationalCutBuffer.denominator,RoundedOracleSearch.rationalNormal]

structure Data {n : ℕ} (r : ℕ) (A C : Finset (Fin n)) (u : ℕ) (σ : Env) : Prop where
  order : σ.vars "graph.n"=n
  count : σ.vars "catalog.count"=N n r
  catalog : Prefix (NativeCatalog.words n r) "catalog.mask" σ
  conditioning : σ.vars "conditioning.choice"=mask A
  component : σ.vars "component.mask"=mask C
  target : σ.vars "component.target"=u

theorem frame {n B K r u : ℕ} {A C : Finset (Fin n)} {c : Com} {σ τ : Env}
    (rr : Run B c σ τ K) (hd : Data r A C u σ)
    (h0 : "graph.n"∉c.wvars) (h1 : "catalog.count"∉c.wvars)
    (h2 : "catalog.mask"∉c.warrs) (h3 : "conditioning.choice"∉c.wvars)
    (h4 : "component.mask"∉c.wvars) (h5 : "component.target"∉c.wvars) : Data r A C u τ := by
  refine ⟨(rr.frame_var _ h0).trans hd.order,(rr.frame_var _ h1).trans hd.count,?_,
    (rr.frame_var _ h3).trans hd.conditioning,(rr.frame_var _ h4).trans hd.component,
    (rr.frame_var _ h5).trans hd.target⟩
  simpa only [Prefix,rr.frame_arr "catalog.mask" h2] using hd.catalog

def read : Com := .seq (.assign "cut.column" (.get "catalog.mask" (.var "fill.i")))
  NativeComponentCoefficient.command

theorem read_spec {n : ℕ} (B r : ℕ) (A C : Finset (Fin n)) (u : ℕ)
    (i : ℕ) (hi : i<(values r A C u).length) (hB : n+u+3*N n r+10<B) (hm : 2^n<B) :
    Spec B (fun σ => Data r A C u σ ∧ σ.vars "fill.i"=i) read
      (fun _ τ => Data r A C u τ ∧ τ.vars "coefficient.positive"<B ∧ τ.vars "coefficient.negative"<B ∧
        ((τ.vars "coefficient.positive" : ℕ) : ℚ)-τ.vars "coefficient.negative"=(values r A C u)[i])
      (28*n+17) := by
  let j : Fin (N n r) := ⟨i,by simpa only [values,List.length_ofFn] using hi⟩
  let J := CoordinateCatalog.indexing n r j
  rintro σ ⟨hd,hidx⟩
  have hlen : (NativeCatalog.words n r).length=N n r := by simp [NativeCatalog.words]
  have hic : i<(NativeCatalog.words n r).length := by rw [hlen]; exact j.isLt
  have hget := hd.catalog i hic
  have hw : (NativeCatalog.words n r)[i]=mask J.val := by
    simp only [NativeCatalog.words,List.getElem_map]
    rfl
  rw [hw] at hget
  let ν := σ.setVar "cut.column" (mask J.val)
  have r1 : Run B (.assign "cut.column" (.get "catalog.mask" (.var "fill.i"))) σ ν 3 :=
    Run.assign (evalB_get (by rw [evalB_var_iff]; exact ⟨hidx.symm,hidx ▸ (by have hj:=j.isLt; omega)⟩)
      hget ((mask_bound _).trans hm))
  have d1 := frame r1 hd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨τ,r2,p2⟩ := NativeComponentCoefficient.command_spec B A C J u (by omega) hm ν
    ⟨d1.order,d1.conditioning,d1.component,by simp [ν],d1.target⟩
  exact ⟨τ,(r1.seq r2).mono (by omega),
    frame r2 d1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    p2.2.1,p2.2.2.1,by simpa only [values,List.getElem_ofFn,RoundedOracleSearch.rationalNormal,normal,MomentLP.encode] using p2.2.2.2⟩

def table : Com := .seq (.assign "fill.length" (.var "catalog.count"))
  (.seq (.assign "lp.length" (.lit 0)) (NativeRationalTabulate.command read))

theorem table_spec {n : ℕ} (B r : ℕ) (A C : Finset (Fin n)) (u : ℕ)
    (hB : n+u+3*N n r+10<B) (hm : 2^n<B) :
    Spec B (fun σ => Data r A C u σ ∧ 3*N n r≤(σ.arrs "lp.input").length) table
      (fun _ τ => Data r A C u τ ∧ τ.vars "lp.length"=3*N n r ∧
        Prefix (NativeRoundedQuery.normal (normal (r:=r) A C u)) "lp.input" τ)
      ((28*n+56)*N n r+10) := by
  have hlen : (values r A C u).length=N n r := List.length_ofFn
  have ht := NativeRationalTabulate.command_spec B (values r A C u) [] (Data r A C u) read (28*n+17)
    (by simp only [List.length_nil,Nat.zero_add,hlen]; omega)
    (by decide) (by decide) (by decide) (by decide)
    (by
      intro σ hd
      exact ⟨by simpa using hd.order,by simpa using hd.count,hd.catalog,
        by simpa using hd.conditioning,by simpa using hd.component,by simpa using hd.target⟩)
    (fun _ _ rr hd => frame rr hd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (fun _ _ rr hd => frame rr hd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (fun i hi => read_spec B r A C u i hi hB hm)
  rintro σ ⟨hd,hroom⟩
  let ν := σ.setVar "fill.length" (N n r)
  have r1 : Run B (.assign "fill.length" (.var "catalog.count")) σ ν 2 := Run.assign
    (by rw [evalB_var_iff]; exact ⟨hd.count.symm,hd.count ▸ (by omega)⟩)
  let μ := ν.setVar "lp.length" 0
  have r2 : Run B (.assign "lp.length" (.lit 0)) ν μ 2 := Run.assign (evalB_lit (show 0<B by omega))
  have d2 := frame (r1.seq r2) hd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨τ,r3,p3⟩ := ht μ ⟨d2,by simp [μ,ν,hlen],by simp [μ],
    by simpa only [List.length_nil,Nat.zero_add,hlen,μ,ν,arrs_setVar] using hroom,by simp [Prefix]⟩
  refine ⟨τ,(r1.seq (r2.seq r3)).mono (by rw [hlen]; nlinarith only []),p3.1,?_,?_⟩
  · simpa only [List.length_nil,Nat.zero_add,hlen] using p3.2.1
  · exact p3.2.2

def command : Com := .seq table (NativeProgramCache.copy "lp.input" "round.normal" "lp.length")

/-- Construct the actual collected component cut, in moment-catalog order,
and store the exact integer normal consumed by the rounded update. -/
theorem command_spec {n : ℕ} (B r : ℕ) (A C : Finset (Fin n)) (u : ℕ)
    (hB : n+u+3*N n r+10<B) (hm : 2^n<B) :
    Spec B (fun σ => Data r A C u σ ∧ NativeArrayBounds.Bounded B σ ∧
      3*N n r≤(σ.arrs "lp.input").length ∧ 3*N n r≤(σ.arrs "round.normal").length) command
      (fun _ τ => Data r A C u τ ∧ Prefix (NativeRoundedQuery.normal
        (RationalCutBuffer.integerNormal (RoundedOracleSearch.rationalNormal (normal (r:=r) A C u)))) "round.normal" τ)
      ((28*n+104)*N n r+20) := by
  rintro σ ⟨hd,hb,hlp,hr⟩
  obtain ⟨ν,r1,p1⟩ := table_spec B r A C u hB hm σ ⟨hd,hlp⟩
  have hlen : (NativeRoundedQuery.normal (normal (r:=r) A C u)).length=3*N n r :=
    NativeRoundedQuery.vector_length _
  obtain ⟨τ,r2,p2⟩ := NativeProgramCache.copy_spec B "lp.input" "round.normal" "lp.length"
    (NativeRoundedQuery.normal (normal (r:=r) A C u)) (by decide) (by rw [hlen]; omega)
    (NativeArrayBounds.prefix_words (NativeArrayBounds.run r1 hb) p1.2.2) ν
    ⟨p1.2.2,by simpa only [hlen] using p1.2.1,by rw [hlen,RamFrames.run_array_length r1]; exact hr⟩
  refine ⟨τ,(r1.seq r2).mono (by rw [hlen]; nlinarith only []),
    frame r2 p1.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),?_⟩
  simpa only [cleared_integer] using p2.2

end Lax263307Proofs.NativeComponentNormal
