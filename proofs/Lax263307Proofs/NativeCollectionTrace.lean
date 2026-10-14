import Lax263307Proofs.NativeComponentTrace
import Lax263307Proofs.NativeCollectionSemantics

namespace Lax263307Proofs.NativeCollectionTrace

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 ComputedRounding NativeCoreMachine NativeMachineSegment NativeMasks

/-- The collection invariant at the top of phase 9. -/
def At {n : ℕ} (Q : Env → Prop) (i : ℕ) (S : Finset (Fin n)) (σ : Env) : Prop :=
  Q σ ∧ σ.vars "component.i"=i ∧ σ.vars "component.union"=mask S ∧
    σ.vars "machine.running"=1 ∧ σ.vars "machine.phase"=9

def ResultOutput {n : ℕ} (Q : Env → Prop) (cut : Finset (Fin n) → ℕ → Env → Prop)
    (result : Result n) (σ : Env) : Prop := Q σ ∧ match result with
  | .found I => NativeRoundTrace.Stopped (some I) σ
  | .cut C u => σ.vars "machine.running"=1 ∧ σ.vars "machine.phase"=13 ∧ cut C u σ

/-- One actual part iteration. Light parts return the empty set; a heavy
part includes its complete child call, recursive execution and restored
reply. The caller obtains this premise from the concrete component/child
phase lemmas and the induction hypothesis on recursion fuel. -/
def Iterations {n : ℕ} {ι : Type} (B : ℕ) (cfg : Config) (Q : Env → Prop)
    (cut : Finset (Fin n) → ℕ → Env → Prop) (parts : ι → Finset (Fin n)) (bound : ι → ℕ)
    (reply : ι → Option (Finset (Fin n))) (order : List ι) (S K : ℕ) : Prop :=
  ∀ (pre : List ι) (i : ι) (suffix : List ι),pre++i::suffix=order →
    ∀ U σ,At Q pre.length U σ →
    ∃ τ transitions total,Segment B (phases cfg) transitions total σ τ ∧
      transitions≤S ∧ total≤K ∧
      match reply i with
      | none => ResultOutput Q cut (.cut (parts i) (bound i)) τ
      | some I => At Q (pre.length+1) (U∪I) τ

theorem loop_segment {n : ℕ} {ι : Type} (B : ℕ) (cfg : Config) (Q : Env → Prop)
    (cut : Finset (Fin n) → ℕ → Env → Prop) (parts : ι → Finset (Fin n)) (bound : ι → ℕ)
    (reply : ι → Option (Finset (Fin n))) (order : List ι) (S K : ℕ)
    (hB : 2*order.length+16<B) (hm : 2^n<B)
    (hcount : ∀ σ,Q σ → σ.vars "component.count"=order.length)
    (hfinish : ∀ σ τ t,Run B (NativeComponentControl.finish 14) σ τ t → Q σ → Q τ)
    (hsteps : Iterations B cfg Q cut parts bound reply order S K) :
    ∀ suffix pre,pre++suffix=order → ∀ U σ,At Q pre.length U σ →
      ∃ τ transitions total,Segment B (phases cfg) transitions total σ τ ∧
        transitions≤S*suffix.length+1 ∧ total≤K*suffix.length+10 ∧
        ResultOutput Q cut (NativeCollectionSemantics.loop parts bound reply suffix U) τ := by
  intro suffix
  induction suffix with
  | nil =>
    intro pre hp U σ hin
    have hlen : pre.length=order.length := by simpa using congrArg List.length hp
    obtain ⟨τ,rr,po⟩ := NativeComponentControl.finish_spec B 14 U (by omega) hm σ hin.2.2.1
    have ht : (Cond.lt (.var "component.i") (.var "component.count")).evalB B σ=some false := by
      have ei : (Expr.var "component.i").evalB B σ=some pre.length := by
        rw [evalB_var_iff]; exact ⟨hin.2.1.symm,hin.2.1 ▸ (by omega)⟩
      have ec : (Expr.var "component.count").evalB B σ=some order.length := by
        rw [evalB_var_iff]; exact ⟨(hcount σ hin.1).symm,(hcount σ hin.1) ▸ (by omega)⟩
      simpa only [hlen,lt_self_iff_false,decide_false] using evalB_condLt ei ec
    have run : Run B component σ τ 10 :=
      (Run.ite_false (c:=.seq NativeComponentLoad.command (go 10)) ht rr).mono (by simp [Cond.size,Expr.size])
    refine ⟨τ,1,10,NativeMachineSegment.phase hin.2.2.2.1 ⟨9,by change 9<16; decide⟩ hin.2.2.2.2 run,
      by simp,by simp,hfinish σ τ 6 rr hin.1,?_,po.2,po.1⟩
    exact (rr.frame_var _ (by decide)).trans hin.2.2.2.1
  | cons i suffix ih =>
    intro pre hp U σ hin
    obtain ⟨ν,s,t,first,hs,ht,ho⟩ := hsteps pre i suffix hp U σ hin
    cases he : reply i with
    | none =>
      refine ⟨ν,s,t,first,by simp only [List.length_cons]; nlinarith only [hs],
        by simp only [List.length_cons]; nlinarith only [ht],?_⟩
      simpa only [NativeCollectionSemantics.loop,he] using ho
    | some I =>
      have hnext : At Q (pre++[i]).length (U∪I) ν := by
        simpa only [he,List.length_append,List.length_singleton] using ho
      have horder : (pre++[i])++suffix=order := by simpa only [List.append_assoc,List.singleton_append] using hp
      obtain ⟨τ,s',t',rest,hs',ht',hout⟩ := ih (pre++[i]) horder (U∪I) ν hnext
      refine ⟨τ,s+s',t+t',NativeMachineSegment.append first rest,
        by simp only [List.length_cons]; nlinarith only [hs,hs'],
        by simp only [List.length_cons]; nlinarith only [ht,ht'],?_⟩
      simpa only [NativeCollectionSemantics.loop,he] using hout

theorem collect_segment {n : ℕ} {ι : Type} [Fintype ι]
    (B : ℕ) (cfg : Config) (Q : Env → Prop) (cut : Finset (Fin n) → ℕ → Env → Prop)
    (parts : ι → Finset (Fin n)) (δ : ℚ) (k : ℕ) (cost : ι → ℚ)
    (query : ι → ℕ → Option (Finset (Fin n))) (order : List ι) (complete : ∀ i,i∈order) (S K : ℕ)
    (hB : 2*order.length+16<B) (hm : 2^n<B)
    (hcount : ∀ σ,Q σ → σ.vars "component.count"=order.length)
    (hfinish : ∀ σ τ t,Run B (NativeComponentControl.finish 14) σ τ t → Q σ → Q τ)
    (hsteps : Iterations B cfg Q cut parts (fun i => target δ (cost i)-1)
      (answer (n:=n) δ k cost query) order S K) (σ : Env) (hin : At (n:=n) Q 0 ∅ σ) :
    ∃ τ transitions total,Segment B (phases cfg) transitions total σ τ ∧
      transitions≤S*order.length+1 ∧ total≤K*order.length+10 ∧
      ResultOutput Q cut (collect order parts δ k cost query) τ := by
  obtain ⟨τ,s,t,tr,hs,ht,ho⟩ := loop_segment B cfg Q cut parts (fun i => target δ (cost i)-1)
    (answer (n:=n) δ k cost query) order S K hB hm hcount hfinish hsteps order [] (by simp) ∅ σ hin
  exact ⟨τ,s,t,tr,hs,ht,by simpa only [NativeCollectionSemantics.realizes_collect order complete] using ho⟩

end Lax263307Proofs.NativeCollectionTrace
