import Lax263307Proofs.NativeRootTransitions

set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeRootTrace

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 NativeCoreMachine NativeMachineSegment NativeMasks

def RootStable (B : ℕ) (Q : Env → Prop) : Prop :=
  ∀ (σ τ : Env) (t : ℕ) (c : Com),c∈[rootTarget,rootReply] → Run B c σ τ t → Q σ → Q τ

/-- Contract to be supplied by the recursive node execution proof.
The trace stops before the root-reply phase, retaining the root target. -/
def Attempts {n : ℕ} (B : ℕ) (cfg : Config) (Q : Env → Prop)
    (attempt : ℕ → Option (Finset (Fin n))) (fuel S K : ℕ) : Prop :=
  ∀ k,0<k → k≤n → ∀ σ,Q σ → σ.vars "node.k"=k → σ.vars "recursion.fuel"=fuel →
    σ.vars "root.target"=k → σ.vars "root.fuel"=fuel →
    σ.vars "machine.running"=1 → σ.vars "machine.phase"=1 →
    ∃ τ steps total,Segment B (phases cfg) steps total σ τ ∧ steps≤S ∧ total≤K ∧ Q τ ∧
      τ.vars "root.target"=k ∧ τ.vars "root.fuel"=fuel ∧ τ.vars "machine.running"=1 ∧
      τ.vars "machine.phase"=15 ∧ NativeTargetDriver.Reply (attempt k) τ

def Answer {n : ℕ} (answer : Finset (Fin n) × ℕ) (σ : Env) : Prop :=
  σ.vars "root.mask"=mask answer.1 ∧ σ.vars "root.value"=answer.2 ∧ σ.vars "machine.running"=0

/-- Descending targets execute in the actual finite dispatcher. Each
attempt may contain arbitrary nested child segments, charged by S and K. -/
theorem search_segment {n : ℕ} (B : ℕ) (cfg : Config) (Q : Env → Prop)
    (attempt : ℕ → Option (Finset (Fin n))) (fuel S K : ℕ)
    (hB : n+fuel+20<B) (hm : 2^n<B) (hstable : RootStable B Q)
    (hattempt : Attempts B cfg Q attempt fuel S K) (k : ℕ) (hk : k≤n) :
    ∀ σ,Q σ → σ.vars "root.target"=k → σ.vars "root.fuel"=fuel →
      σ.vars "machine.running"=1 → σ.vars "machine.phase"=0 →
      ∃ τ steps total,Segment B (phases cfg) steps total σ τ ∧
        steps≤(S+2)*k+1 ∧ total≤(K+20)*k+10 ∧ Q τ ∧ Answer (TargetSearch.search attempt k) τ := by
  induction k with
  | zero =>
    intro σ hQ ht hf hr hp
    obtain ⟨τ,rr,p⟩ := NativeRootTransitions.target_zero_spec B (by omega) σ ht
    have trace : Segment B (phases cfg) 1 10 σ τ :=
      phase hr ⟨0,by rw [phases_length]; decide⟩ hp rr
    refine ⟨τ,1,10,trace,by omega,by omega,hstable σ τ 10 rootTarget (by simp) rr hQ,?_⟩
    simpa only [Answer,TargetSearch.search,mask_empty] using p
  | succ k ih =>
    intro σ hQ ht hf hr hp
    obtain ⟨ν,r0,p0⟩ := NativeRootTransitions.target_positive_spec B (k+1) fuel (by omega) (by omega) σ ⟨ht,hf⟩
    have first : Segment B (phases cfg) 1 10 σ ν :=
      phase hr ⟨0,by rw [phases_length]; decide⟩ hp r0
    have hQν := hstable σ ν 10 rootTarget (by simp) r0 hQ
    have htν := (r0.frame_var "root.target" (by decide)).trans ht
    have hfν := (r0.frame_var "root.fuel" (by decide)).trans hf
    have hrν := p0.2.2.2.trans hr
    obtain ⟨μ,s,t,middle,hs,hcost,hQμ,htμ,hfμ,hrμ,hpμ,hreply⟩ :=
      hattempt (k+1) (by omega) hk ν hQν p0.1 p0.2.1 htν hfν hrν p0.2.2.1
    cases ha : attempt (k+1) with
    | none =>
      have htag : μ.vars "recursion.return.tag"=0 := by simpa only [ha,NativeTargetDriver.Reply] using hreply
      obtain ⟨ρ,r1,p1⟩ := NativeRootTransitions.reply_none_spec B k (by omega) μ ⟨htag,htμ⟩
      have reply : Segment B (phases cfg) 1 10 μ ρ :=
        phase hrμ ⟨15,by rw [phases_length]; decide⟩ hpμ r1
      have hQρ := hstable μ ρ 10 rootReply (by simp) r1 hQμ
      have hfρ := (r1.frame_var "root.fuel" (by decide)).trans hfμ
      obtain ⟨τ,s',t',rest,hs',ht',hQτ,hanswer⟩ := ih (by omega) ρ hQρ p1.1 hfρ (p1.2.2.trans hrμ) p1.2.1
      have trace := NativeMachineSegment.append (NativeMachineSegment.append (NativeMachineSegment.append first middle) reply) rest
      refine ⟨τ,1+s+1+s',10+t+10+t',trace,by nlinarith only [hs,hs'],by nlinarith only [hcost,ht'],hQτ,?_⟩
      simpa only [TargetSearch.search,ha] using hanswer
    | some I =>
      have htag : NativeTargetDriver.Reply (some I) μ := by simpa only [ha] using hreply
      obtain ⟨τ,r1,p1⟩ := NativeRootTransitions.reply_some_spec B (k+1) I (by omega) hm μ ⟨htag,htμ⟩
      have reply : Segment B (phases cfg) 1 10 μ τ :=
        phase hrμ ⟨15,by rw [phases_length]; decide⟩ hpμ r1
      have trace := NativeMachineSegment.append (NativeMachineSegment.append first middle) reply
      refine ⟨τ,1+s+1,10+t+10,trace,by nlinarith only [hs],by nlinarith only [hcost],
        hstable μ τ 10 rootReply (by simp) r1 hQμ,?_⟩
      simpa only [Answer,TargetSearch.search,ha] using p1

theorem driver_spec {n : ℕ} (B : ℕ) (cfg : Config) (Q : Env → Prop)
    (attempt : ℕ → Option (Finset (Fin n))) (fuel S K : ℕ)
    (hB : n+fuel+20<B) (hm : 2^n<B) (hstable : RootStable B Q)
    (hattempt : Attempts B cfg Q attempt fuel S K) :
    Spec B (fun σ => Q σ ∧ σ.vars "root.target"=n ∧ σ.vars "root.fuel"=fuel ∧
      σ.vars "machine.running"=1 ∧ σ.vars "machine.phase"=0)
      (NativeMachineTrace.driver (phases cfg))
      (fun _ τ => Q τ ∧ Answer (TargetSearch.search attempt n) τ)
      ((K+20+68*(S+2))*n+82) := by
  rintro σ ⟨hQ,ht,hf,hr,hp⟩
  obtain ⟨τ,s,t,trace,hs,hcost,hQτ,answer⟩ := search_segment B cfg Q attempt fuel S K hB hm hstable hattempt n
    (by rfl) σ hQ ht hf hr hp
  have rr := NativeCoreMachine.driver_run trace answer.2.2 (by omega)
  exact ⟨τ,rr.mono (by nlinarith only [hs,hcost]),hQτ,answer⟩

end Lax263307Proofs.NativeRootTrace
