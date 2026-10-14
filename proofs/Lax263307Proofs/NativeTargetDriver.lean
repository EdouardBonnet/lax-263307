import Lax263307Proofs.NativeMasks
import Lax263307.TargetSearch

namespace Lax263307Proofs.NativeTargetDriver

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 NativeMasks

def privateVars : List String := ["target.i","target.k","target.done","target.mask","target.value"]

def Reply {n : ℕ} (answer : Option (Finset (Fin n))) (σ : Env) : Prop :=
  match answer with
  | none => σ.vars "recursion.return.tag"=0
  | some I => σ.vars "recursion.return.tag"=1 ∧ σ.vars "recursion.return.mask"=mask I

def Outcome {n : ℕ} (attempt : ℕ → Option (Finset (Fin n))) (i : ℕ) (σ : Env) : Prop :=
  (σ.vars "target.done"=0 ∧ σ.vars "target.mask"=0 ∧ σ.vars "target.value"=0 ∧
    TargetSearch.search attempt n=TargetSearch.search attempt (n-i)) ∨
  ∃ I t,σ.vars "target.done"=1 ∧ σ.vars "target.mask"=mask I ∧ σ.vars "target.value"=t ∧
    TargetSearch.search attempt n=(I,t)

def saveResult : Com := .seq (.assign "target.mask" (.var "recursion.return.mask"))
  (.seq (.assign "target.value" (.var "target.k")) (.assign "target.done" (.lit 1)))

def choose : Com := .ite (.eq (.var "recursion.return.tag") (.lit 1)) saveResult .skip
def active (body : Com) : Com := .seq (.assign "target.k" (.sub (.var "graph.n") (.var "target.i")))
  (.seq body choose)
def step (body : Com) : Com := .seq (.ite (.eq (.var "target.done") (.lit 0)) (active body) .skip)
  (.assign "target.i" (.add (.var "target.i") (.lit 1)))

def Invariant {n : ℕ} (Q : Env → Prop) (attempt : ℕ → Option (Finset (Fin n))) (σ : Env) : Prop :=
  Q σ ∧ σ.vars "target.i"≤n ∧ Outcome attempt (σ.vars "target.i") σ

theorem save_result_spec {n : ℕ} (B k : ℕ) (I : Finset (Fin n)) (Q : Env → Prop)
    (hB : n+2<B) (hm : 2^n<B) (hk : k≤n)
    (hset : ∀ σ s v,s∈privateVars → Q σ → Q (σ.setVar s v)) :
    Spec B (fun σ => Q σ ∧ σ.vars "recursion.return.mask"=mask I ∧ σ.vars "target.k"=k) saveResult
      (fun _ τ => Q τ ∧ τ.vars "target.done"=1 ∧ τ.vars "target.mask"=mask I ∧ τ.vars "target.value"=k) 6 := by
  rintro σ ⟨hQ,hr,ht⟩
  let ν := σ.setVar "target.mask" (mask I)
  have r1 : Run B (.assign "target.mask" (.var "recursion.return.mask")) σ ν 2 := Run.assign
    (by rw [evalB_var_iff]; exact ⟨hr.symm,hr ▸ (mask_bound I).trans hm⟩)
  let μ := ν.setVar "target.value" k
  have htν := (r1.frame_var "target.k" (by decide)).trans ht
  have r2 : Run B (.assign "target.value" (.var "target.k")) ν μ 2 := Run.assign
    (by rw [evalB_var_iff]; exact ⟨htν.symm,htν ▸ (by omega : k<B)⟩)
  let τ := μ.setVar "target.done" 1
  have r3 : Run B (.assign "target.done" (.lit 1)) μ τ 2 := Run.assign (evalB_lit (show 1<B by omega))
  have hQτ := hset μ "target.done" 1 (by simp [privateVars])
    (hset ν "target.value" k (by simp [privateVars]) (hset σ "target.mask" (mask I) (by simp [privateVars]) hQ))
  exact ⟨τ,r1.seq (r2.seq r3),hQτ,by simp [τ],by simp [τ,μ,ν],by simp [τ,μ]⟩

theorem active_spec {n : ℕ} (B K : ℕ) (Q : Env → Prop) (attempt : ℕ → Option (Finset (Fin n)))
    (body : Com) (hB : n+2<B) (hm : 2^n<B)
    (horder : ∀ σ,Q σ → σ.vars "graph.n"=n)
    (hset : ∀ σ s v,s∈privateVars → Q σ → Q (σ.setVar s v))
    (hbody : ∀ k,0<k → k≤n → Spec B (fun σ => Q σ ∧ σ.vars "target.k"=k) body
      (fun _ τ => Q τ ∧ Reply (attempt k) τ) K)
    (hprotect : ∀ s∈privateVars,s∉body.wvars) :
    Spec B (fun σ => Invariant Q attempt σ ∧ σ.vars "target.i"<n ∧ σ.vars "target.done"=0)
      (active body) (fun σ τ => Q τ ∧ Outcome attempt (σ.vars "target.i"+1) τ ∧
        τ.vars "target.i"=σ.vars "target.i") (K+14) := by
  rintro σ ⟨⟨hQ,hle,hout⟩,hi,hdone⟩
  let i := σ.vars "target.i"
  let k := n-i
  have hk : 0<k := by dsimp [k,i]; omega
  have hkn : k≤n := Nat.sub_le _ _
  have hnext : k=(n-(i+1))+1 := by dsimp [k,i]; omega
  have hrun : σ.vars "target.mask"=0 ∧ σ.vars "target.value"=0 ∧
      TargetSearch.search attempt n=TargetSearch.search attempt k := by
    rcases hout with ⟨_,hm,hv,he⟩ | ⟨I,t,hd,rest⟩
    · exact ⟨hm,hv,he⟩
    · omega
  let ν := σ.setVar "target.k" k
  have r1 : Run B (.assign "target.k" (.sub (.var "graph.n") (.var "target.i"))) σ ν 4 := Run.assign
    (evalB_bin (op:=.sub)
      (by rw [evalB_var_iff]; exact ⟨(horder σ hQ).symm,(horder σ hQ) ▸ (by omega : n<B)⟩)
      (evalB_var (by omega)) (by change n-i<B; omega))
  have hQν := hset σ "target.k" k (by simp [privateVars]) hQ
  obtain ⟨μ,r2,p2⟩ := hbody k hk hkn ν ⟨hQν,by simp [ν]⟩
  have hiμ : μ.vars "target.i"=i := (r1.seq r2).frame_var "target.i" (by
    simp [Com.wvars,hprotect "target.i" (by simp [privateVars])])
  have hkμ : μ.vars "target.k"=k := (r2.frame_var "target.k" (hprotect _ (by simp [privateVars]))).trans (by simp [ν])
  cases ha : attempt k with
  | none =>
    have htag : μ.vars "recursion.return.tag"=0 := by simpa only [Reply,ha] using p2.2
    have hc : (Cond.eq (.var "recursion.return.tag") (.lit 1)).evalB B μ=some false := by
      have hh := evalB_condEq
        (by rw [evalB_var_iff]; exact ⟨htag.symm,htag ▸ (by omega : 0<B)⟩) (evalB_lit (show 1<B by omega))
      simpa using hh
    have r3 : Run B choose μ μ 10 := (Run.ite_false (c:=saveResult) hc Run.skip).mono (by decide)
    have rr := r1.seq (r2.seq r3)
    have htrace : TargetSearch.search attempt k=TargetSearch.search attempt (n-(i+1)) := by
      rw [hnext,TargetSearch.search]
      simpa only [← hnext,ha]
    refine ⟨μ,rr.mono (by omega),p2.1,Or.inl ⟨?_,?_,?_,hrun.2.2.trans htrace⟩,hiμ⟩
    · exact ((r1.seq r2).frame_var "target.done" (by simp [Com.wvars,hprotect "target.done" (by simp [privateVars])])).trans hdone
    · exact ((r1.seq r2).frame_var "target.mask" (by simp [Com.wvars,hprotect "target.mask" (by simp [privateVars])])).trans hrun.1
    · exact ((r1.seq r2).frame_var "target.value" (by simp [Com.wvars,hprotect "target.value" (by simp [privateVars])])).trans hrun.2.1
  | some I =>
    have htag : μ.vars "recursion.return.tag"=1 ∧ μ.vars "recursion.return.mask"=mask I := by simpa only [Reply,ha] using p2.2
    have hc : (Cond.eq (.var "recursion.return.tag") (.lit 1)).evalB B μ=some true := by
      have hh := evalB_condEq
        (by rw [evalB_var_iff]; exact ⟨htag.1.symm,htag.1 ▸ (by omega : 1<B)⟩) (evalB_lit (show 1<B by omega))
      simpa using hh
    obtain ⟨τ,rs,ps⟩ := save_result_spec B k I Q hB hm hkn hset μ ⟨p2.1,htag.2,hkμ⟩
    have r3 : Run B choose μ τ 10 := (Run.ite_true (d:=.skip) hc rs).mono (by decide)
    have htrace : TargetSearch.search attempt k=(I,k) := by
      rw [hnext,TargetSearch.search]
      simpa only [← hnext,ha]
    exact ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),ps.1,
      Or.inr ⟨I,k,ps.2.1,ps.2.2.1,ps.2.2.2,hrun.2.2.trans htrace⟩,
      (r3.frame_var "target.i" (by decide)).trans hiμ⟩

theorem outcome_frame {B K n : ℕ} {attempt : ℕ → Option (Finset (Fin n))} {i : ℕ}
    {c : Com} {σ τ : Env} (rr : Run B c σ τ K) (ho : Outcome attempt i σ)
    (hd : "target.done"∉c.wvars) (hm : "target.mask"∉c.wvars) (hv : "target.value"∉c.wvars) :
    Outcome attempt i τ := by
  rcases ho with ⟨hdone,hmask,hvalue,he⟩ | ⟨I,t,hdone,hmask,hvalue,he⟩
  · exact Or.inl ⟨(rr.frame_var _ hd).trans hdone,(rr.frame_var _ hm).trans hmask,
      (rr.frame_var _ hv).trans hvalue,he⟩
  · exact Or.inr ⟨I,t,(rr.frame_var _ hd).trans hdone,(rr.frame_var _ hm).trans hmask,
      (rr.frame_var _ hv).trans hvalue,he⟩

theorem step_spec {n : ℕ} (B K : ℕ) (Q : Env → Prop) (attempt : ℕ → Option (Finset (Fin n)))
    (body : Com) (hB : n+2<B) (hm : 2^n<B)
    (horder : ∀ σ,Q σ → σ.vars "graph.n"=n)
    (hset : ∀ σ s v,s∈privateVars → Q σ → Q (σ.setVar s v))
    (hbody : ∀ k,0<k → k≤n → Spec B (fun σ => Q σ ∧ σ.vars "target.k"=k) body
      (fun _ τ => Q τ ∧ Reply (attempt k) τ) K)
    (hprotect : ∀ s∈privateVars,s∉body.wvars) :
    Spec B (fun σ => Invariant Q attempt σ ∧ σ.vars "target.i"<n) (step body)
      (fun σ τ => Invariant Q attempt τ ∧ τ.vars "target.i"=σ.vars "target.i"+1) (K+22) := by
  rintro σ ⟨hd,hi⟩
  let i := σ.vars "target.i"
  have hc : (Cond.eq (.var "target.done") (.lit 0)).evalB B σ=some (decide (σ.vars "target.done"=0)) := by
    have hdone : σ.vars "target.done"<B := by
      rcases hd.2.2 with ⟨h,rest⟩ | ⟨I,t,h,rest⟩ <;> rw [h] <;> omega
    have hh := evalB_condEq (evalB_var hdone) (evalB_lit (show 0<B by omega))
    by_cases h : σ.vars "target.done"=0 <;> simpa [h] using hh
  have hbranch : ∃ μ,Run B (.ite (.eq (.var "target.done") (.lit 0)) (active body) .skip) σ μ (K+18) ∧
      Q μ ∧ Outcome attempt (i+1) μ ∧ μ.vars "target.i"=i := by
    by_cases h : σ.vars "target.done"=0
    · obtain ⟨μ,rr,p⟩ := active_spec B K Q attempt body hB hm horder hset hbody hprotect σ ⟨hd,hi,h⟩
      exact ⟨μ,(Run.ite_true (d:=.skip) (by simpa only [h,decide_true] using hc) rr).mono
        (by simp [Cond.size,Expr.size] <;> omega),p⟩
    · have ho : Outcome attempt (i+1) σ := by
        rcases hd.2.2 with ⟨hzero,rest⟩ | ⟨I,t,rest⟩
        · exact False.elim (h hzero)
        · exact Or.inr ⟨I,t,rest⟩
      exact ⟨σ,(Run.ite_false (c:=active body) (by simpa only [h,decide_false] using hc) Run.skip).mono
        (by simp [Cond.size,Expr.size] <;> omega),hd.1,ho,rfl⟩
  obtain ⟨μ,r1,hQ,ho,hiμ⟩ := hbranch
  let τ := μ.setVar "target.i" (i+1)
  have r2 : Run B (.assign "target.i" (.add (.var "target.i") (.lit 1))) μ τ 4 := Run.assign
    (evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hiμ.symm,hiμ ▸ (by omega : i<B)⟩)
      (evalB_lit (show 1<B by omega)) (by change i+1<B; omega))
  have ht : τ.vars "target.i"=i+1 := by simp [τ]
  exact ⟨τ,(r1.seq r2).mono (by omega),
    ⟨hset μ "target.i" (i+1) (by simp [privateVars]) hQ,by rw [ht]; omega,
      by rw [ht]; exact outcome_frame r2 ho (by decide) (by decide) (by decide)⟩,ht⟩

def command (body : Com) : Com := .seq (.assign "target.done" (.lit 0))
  (.seq (.assign "target.mask" (.lit 0)) (.seq (.assign "target.value" (.lit 0))
    (.seq (.assign "target.i" (.lit 0)) (.while (.lt (.var "target.i") (.var "graph.n")) (step body)))))

/-- Descending target search by one fixed bounded native loop. Once a
target succeeds the saved answer is retained through the remaining iterations. -/
theorem command_spec {n : ℕ} (B K : ℕ) (Q : Env → Prop) (attempt : ℕ → Option (Finset (Fin n)))
    (body : Com) (hB : n+2<B) (hm : 2^n<B)
    (horder : ∀ σ,Q σ → σ.vars "graph.n"=n)
    (hset : ∀ σ s v,s∈privateVars → Q σ → Q (σ.setVar s v))
    (hbody : ∀ k,0<k → k≤n → Spec B (fun σ => Q σ ∧ σ.vars "target.k"=k) body
      (fun _ τ => Q τ ∧ Reply (attempt k) τ) K)
    (hprotect : ∀ s∈privateVars,s∉body.wvars) :
    Spec B Q (command body) (fun _ τ => Q τ ∧
      τ.vars "target.mask"=mask (TargetSearch.search attempt n).1 ∧
      τ.vars "target.value"=(TargetSearch.search attempt n).2) ((K+26)*n+12) := by
  have hloop := Spec.forRangeZero "target.i" "graph.n" (Invariant Q attempt) n (K+22) (by omega)
    (fun _ h => h.2.1) (fun σ h => horder σ h.1) (step_spec B K Q attempt body hB hm horder hset hbody hprotect)
  intro σ hQ
  let ν := σ.setVar "target.done" 0
  let μ := ν.setVar "target.mask" 0
  let ρ := μ.setVar "target.value" 0
  have r1 : Run B (.assign "target.done" (.lit 0)) σ ν 2 := Run.assign (evalB_lit (show 0<B by omega))
  have r2 : Run B (.assign "target.mask" (.lit 0)) ν μ 2 := Run.assign (evalB_lit (show 0<B by omega))
  have r3 : Run B (.assign "target.value" (.lit 0)) μ ρ 2 := Run.assign (evalB_lit (show 0<B by omega))
  have hQρ := hset μ "target.value" 0 (by simp [privateVars])
    (hset ν "target.mask" 0 (by simp [privateVars]) (hset σ "target.done" 0 (by simp [privateVars]) hQ))
  have hinit : Invariant Q attempt (ρ.setVar "target.i" 0) := by
    refine ⟨hset ρ "target.i" 0 (by simp [privateVars]) hQρ,by simp,Or.inl ⟨?_,?_,?_,?_⟩⟩
    · simp [ρ,μ,ν]
    · simp [ρ,μ]
    · simp [ρ]
    · simp
  obtain ⟨τ,r4,p4⟩ := hloop ρ hinit
  refine ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono (by nlinarith only []),p4.1.1,?_⟩
  have ho : Outcome attempt n τ := by simpa only [p4.2] using p4.1.2.2
  rcases ho with ⟨hd,hm,hv,he⟩ | ⟨I,t,hd,hm,hv,he⟩
  · have hr : TargetSearch.search attempt n=(∅,0) := by simpa only [Nat.sub_self,TargetSearch.search] using he
    rw [hr]
    simpa only [mask_empty] using (show τ.vars "target.mask"=0 ∧ τ.vars "target.value"=0 from ⟨hm,hv⟩)
  · rw [he]
    exact ⟨hm,hv⟩

end Lax263307Proofs.NativeTargetDriver
