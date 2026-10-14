import Lax263307Proofs.NativeCoreMachine

namespace Lax263307Proofs.NativeRoundTrace

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 RoundedOracleSearch NativeCoreMachine NativeMachineSegment

def Stopped {m : ℕ} (answer : Option (Finset (Fin m))) (σ : Env) : Prop :=
  σ.vars "machine.running"=1 ∧ σ.vars "machine.phase"=14 ∧ NativeTargetDriver.Reply answer σ

def Outcome {n m : ℕ} (Q : ℕ → State n → Env → Prop) (limit k : ℕ) (state : State n)
    (reply : Reply n (Finset (Fin m))) (σ : Env) : Prop :=
  match reply with
  | .found I => Stopped (some I) σ
  | .reject => Stopped (none : Option (Finset (Fin m))) σ
  | .cut a => Q (k+1) (update k state a) σ ∧
      if k+1<limit then σ.vars "machine.running"=1 ∧ σ.vars "machine.phase"=4
      else Stopped (none : Option (Finset (Fin m))) σ

/-- One complete oracle/update step, including any nested child segments.
The concrete phase proofs must supply this contract. -/
def Steps {n m : ℕ} (B : ℕ) (cfg : Config) (Base : Env → Prop)
    (Q : ℕ → State n → Env → Prop) (oracle : ℕ → (Fin n → ℚ) → Reply n (Finset (Fin m)))
    (limit S K : ℕ) : Prop :=
  ∀ k,k<limit → ∀ state σ,Q k state σ → σ.vars "machine.running"=1 → σ.vars "machine.phase"=4 →
    ∃ τ steps total,Segment B (phases cfg) steps total σ τ ∧ steps≤S ∧ total≤K ∧ Base τ ∧
      Outcome Q limit k state (oracle k state.2) τ

/-- The bounded round-or-cut scan is realized by actual machine segments.
Its resource use is linear in the numeric number of remaining iterations. -/
theorem scan_segment {n m : ℕ} (B : ℕ) (cfg : Config) (Base : Env → Prop)
    (Q : ℕ → State n → Env → Prop) (oracle : ℕ → (Fin n → ℚ) → Reply n (Finset (Fin m)))
    (limit S K : ℕ) (hsteps : Steps B cfg Base Q oracle limit S K) :
    ∀ remaining,0<remaining → ∀ k,k+remaining=limit → ∀ state σ,Q k state σ →
      σ.vars "machine.running"=1 → σ.vars "machine.phase"=4 →
      ∃ τ steps total,Segment B (phases cfg) steps total σ τ ∧ steps≤S*remaining ∧ total≤K*remaining ∧
        Base τ ∧ Stopped (scan oracle k remaining state) τ := by
  intro remaining
  induction remaining with
  | zero => intro h; omega
  | succ count ih =>
    intro hcount k hlimit state σ hQ hr hp
    obtain ⟨ν,s,t,first,hs,ht,hbase,hout⟩ := hsteps k (by omega) state σ hQ hr hp
    cases ho : oracle k state.2 with
    | found I =>
      refine ⟨ν,s,t,first,by nlinarith only [hs],by nlinarith only [ht],hbase,?_⟩
      simpa only [scan,ho,Outcome] using hout
    | reject =>
      refine ⟨ν,s,t,first,by nlinarith only [hs],by nlinarith only [ht],hbase,?_⟩
      simpa only [scan,ho,Outcome] using hout
    | cut a =>
      have hc : Q (k+1) (update k state a) ν ∧
          if k+1<limit then ν.vars "machine.running"=1 ∧ ν.vars "machine.phase"=4
          else Stopped (none : Option (Finset (Fin m))) ν := by
        simpa only [ho,Outcome] using hout
      cases count with
      | zero =>
        refine ⟨ν,s,t,first,by simpa using hs,by simpa using ht,hbase,?_⟩
        have he : ¬k+1<limit := by omega
        simpa only [scan,ho,he,if_false] using hc.2
      | succ rest =>
        have he : k+1<limit := by omega
        have hnext : ν.vars "machine.running"=1 ∧ ν.vars "machine.phase"=4 := by
          simpa only [he,if_true] using hc.2
        obtain ⟨τ,s',t',second,hs',ht',hbase',hanswer⟩ := ih (by omega) (k+1) (by omega)
          (update k state a) ν hc.1 hnext.1 hnext.2
        refine ⟨τ,s+s',t+t',NativeMachineSegment.append first second,
          by nlinarith only [hs,hs'],by nlinarith only [ht,ht'],hbase',?_⟩
        simpa only [scan,ho] using hanswer

theorem search_segment {n m : ℕ} (B : ℕ) (cfg : Config) (Base : Env → Prop)
    (Q : ℕ → State n → Env → Prop) (oracle : ℕ → (Fin n → ℚ) → Reply n (Finset (Fin m)))
    (precision S K : ℕ) (hsteps : Steps B cfg Base Q oracle (steps n precision) S K) :
    ∀ σ,Q 0 (1,0) σ → σ.vars "machine.running"=1 → σ.vars "machine.phase"=4 →
      ∃ τ transitions total,Segment B (phases cfg) transitions total σ τ ∧
        transitions≤S*steps n precision ∧ total≤K*steps n precision ∧
        Base τ ∧ Stopped (search oracle precision) τ := by
  intro σ hQ hr hp
  exact scan_segment B cfg Base Q oracle (steps n precision) S K hsteps _
    (by unfold steps; positivity) 0 (by omega) (1,0) σ hQ hr hp

end Lax263307Proofs.NativeRoundTrace
