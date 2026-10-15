import Lax263307Proofs.NativeRoundedState
import Lax263307Proofs.NativeOutputWords
import Lax263307Proofs.NativeRawFrame
import Lax263307Proofs.NativeRoundedStep

namespace Lax263307Proofs.NativeRoundedUpdate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 RoundedOracleSearch
open Matrix

def command (p : Lax808846.Ram.Program) : Com := .seq NativeRoundedQuery.command
  (.seq (NativeRawOracle.command p) NativeRoundedState.command)

def timeBound (p : Lax808846.Ram.Program) (c n h k : ℕ) : ℕ :=
  NativeRawOracle.cost p (2+3*(n*n)+6*n) (c*(n+h+k+1)^12)+96*(n*n)+144*n+78

theorem input_length {n : ℕ} (k : ℕ) (state : State n) (a : Fin n → ℤ) :
    (Lax263307.NativeRoundedStep.encodeInput k state a).length=2+3*(n*n)+6*n := by
  change ([n,k]++NativeRoundedQuery.shape state++NativeRoundedQuery.normal a++NativeRoundedQuery.center state).length=_
  simp only [List.length_append,List.length_cons,List.length_nil,Nat.add_zero,NativeRoundedQuery.shape_length,
    NativeRoundedQuery.normal,NativeRoundedQuery.center,NativeRoundedQuery.vector_length]
  omega

/-- One fixed native command reads the persistent current state,
constructs its raw query, invokes the checked rounded update program,
and replaces the stored shape and center by the exact next state. -/
theorem exists_program : ∃ (p : Lax808846.Ram.Program) (c : ℕ),0<c ∧
    ∀ (n k h : ℕ),2≤n → 1≤h →
    ∀ (state : State n) (a : Fin n → ℤ),
    (∀ i j,Lax263307.NativeRoundedStep.height (state.1 i j) h) →
    (∀ i,Lax263307.NativeRoundedStep.height (rationalNormal a i) h) →
    (∀ i,Lax263307.NativeRoundedStep.height (state.2 i) h) →
    0<rationalNormal a ⬝ᵥ (state.1 *ᵥ rationalNormal a) →
    ∀ (B v : ℕ),c*(n+h+k+1)^12≤v →
    let T := c*(n+h+k+1)^12
    let xs := Lax263307.NativeRoundedStep.encodeInput k state a
    2*(2^v)^2+3<B → T+1<B → RamVirtualConstants.allowance p<B → xs.length+3<B →
    (∀ z∈xs,z<B) →
    Spec B (fun σ => NativeRoundedQuery.Data k state a σ ∧ σ.vars "vm.width"=v ∧
      xs.length≤(σ.arrs "vm.input").length ∧ T<(σ.arrs "vm.addresses").length ∧
      T<(σ.arrs "vm.values").length ∧ T<(σ.arrs "vm.output").length ∧
      3*(n*n)≤(σ.arrs "round.shape").length ∧ 3*n≤(σ.arrs "round.center").length)
      (command p) (fun _ τ => Prefix (NativeRoundedQuery.shape (update k state a)) "round.shape" τ ∧
        Prefix (NativeRoundedQuery.center (update k state a)) "round.center" τ ∧
        τ.vars "vec.n"=n ∧ τ.vars "round.i"=k) (timeBound p c n h k) := by
  obtain ⟨p,c,hc,hstep⟩ := Lax263307.NativeRoundedStep.exists_program
  refine ⟨p,c,hc,?_⟩
  intro n k h hn hh state a hA ha hcenter hpos B v hv
  dsimp only
  intro hB hT hp hlen hwords
  obtain ⟨t,ht,hr⟩ := hstep n k h hn hh state a hA ha hcenter hpos v hv
  have hM : 2^v<B := by
    have hs : 2^v≤(2^v)^2 := by simpa only [pow_two] using Nat.le_mul_self (2^v)
    nlinarith only [hB,hs]
  have hy := NativeOutputWords.runs_to_words v p _ _ t hr
  have houtput : ∀ z∈Lax263307.NativeRoundedStep.encodeOutput (update k state a),z<B :=
    fun z hz => (hy z hz).trans hM
  rintro σ ⟨hd,hwidth,hinput,hAroom,hVroom,hOroom,hshaperoom,hcenterroom⟩
  obtain ⟨ν,r1,p1⟩ := NativeRoundedQuery.command_spec B k state a hlen hwords σ hd
  obtain ⟨μ,r2,p2⟩ := NativeRawOracle.command_spec B v (c*(n+h+k+1)^12) p _ _ hB hT hp (by omega) hwords
    ⟨t,ht,hr⟩ ν
    ⟨p1.2.1,p1.2.2,(r1.frame_var "vm.width" (by decide)).trans hwidth,
      by rwa [RamFrames.run_array_length r1],by rwa [RamFrames.run_array_length r1],
      by rwa [RamFrames.run_array_length r1],by rwa [RamFrames.run_array_length r1]⟩
  have hnμ := (r2.frame_var "vec.n" (NativeRawFrame.command_variable p _ (by decide) (by decide))).trans p1.1.order
  obtain ⟨τ,r3,p3⟩ := NativeRoundedState.command_spec B (update k state a)
    (by rw [input_length] at hlen; omega) houtput μ
    ⟨p2.1,hnμ,by rwa [RamFrames.run_array_length r2,RamFrames.run_array_length r1],
      by rwa [RamFrames.run_array_length r2,RamFrames.run_array_length r1]⟩
  refine ⟨τ,(r1.seq (r2.seq r3)).mono ?_,p3.1,p3.2.1,p3.2.2,?_⟩
  · rw [input_length]
    dsimp only [timeBound]
    nlinarith only []
  · exact ((r2.seq r3).frame_var "round.i" (by
      simp only [Com.wvars,List.mem_append,not_or]
      exact ⟨NativeRawFrame.command_variable p _ (by decide) (by decide),by decide⟩)).trans p1.1.index

end Lax263307Proofs.NativeRoundedUpdate
