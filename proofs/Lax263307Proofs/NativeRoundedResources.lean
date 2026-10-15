import Lax263307Proofs.NativeOracleRounds
import Lax263307Proofs.NativeRationalBounds

set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeRoundedResources

open Lax263307 RoundedOracleSearch Matrix

def buffers : List String := ["lp.word","vm.input","vm.addresses","vm.values",
  "vm.output","round.shape","round.center"]

def space (c R H : ℕ) : ℕ := c*(2*R+H+1)^12+3*R*R+6*R+10

def wordHeight (p : Lax808846.Ram.Program) (v R H : ℕ) : ℕ :=
  2*v+H+Lax455465Proofs.RamVirtualConstants.allowance p+3*R*R+8*R+100

theorem input_words {N : ℕ} (j H B : ℕ) (state : State N) (a : Fin N → ℤ)
    (hN : N<B) (hj : j<B) (h1 : 1<B) (hH : 2^H<B)
    (hs : ∀ i k,NativeRoundedStep.height (state.1 i k) H)
    (ha : ∀ i,NativeRoundedStep.height (rationalNormal a i) H)
    (hc : ∀ i,NativeRoundedStep.height (state.2 i) H) :
    ∀ z∈NativeRoundedStep.encodeInput j state a,z<B := by
  have vec := NativeRationalBounds.vector_words B (2^H) N
  intro z hz
  change z∈[N,j]++NativeRoundedQuery.shape state++NativeRoundedQuery.normal a++
    NativeRoundedQuery.center state at hz
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with (((rfl|rfl)|hz)|hz)|hz
  · exact hN
  · exact hj
  · simp only [NativeRoundedQuery.shape,List.mem_flatten,List.mem_ofFn] at hz
    obtain ⟨row,⟨i,rfl⟩,hz⟩ := hz
    exact vec (state.1 i) h1 hH (hs i) z hz
  · exact vec (rationalNormal a) h1 hH ha z hz
  · exact vec state.2 h1 hH hc z hz

/-- Uniform rounded-update guards from root bounds on the actual state
and cut heights. The host width is independent of their derivation. -/
theorem bounds {N : ℕ} (p : Lax808846.Ram.Program) (c H v m j limit R w : ℕ)
    (extent : String → ℕ) (state : State N) (a : Fin N → ℤ)
    (hN : 2≤N) (hH : 1≤H) (hNR : N≤R) (hmR : m≤R) (hjR : j≤R) (hlR : limit≤R)
    (hs : ∀ i k,NativeRoundedStep.height (state.1 i k) H)
    (ha : ∀ i,NativeRoundedStep.height (rationalNormal a i) H)
    (hc : ∀ i,NativeRoundedStep.height (state.2 i) H)
    (positive : 0<dotProduct (rationalNormal a) (state.1 *ᵥ rationalNormal a))
    (hv : c*(2*R+H+1)^12≤v) (hw : wordHeight p v R H≤w)
    (room : ∀ s∈buffers,space c R H≤extent s) :
    NativeOracleRounds.Bounds (2^w) c H v m j limit p extent state a := by
  have hNN : N*N≤R*R := Nat.mul_self_le_mul_self hNR
  have ht : c*(N+H+j+1)^12≤c*(2*R+H+1)^12 := Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by omega) 12)
  have hsize := NativeRoundedUpdate.input_length j state a
  have hbase : 2*v+H+Lax455465Proofs.RamVirtualConstants.allowance p+3*R*R+8*R+100≤w := hw
  have wlt : w<2^w := Nat.lt_two_pow_self
  have hwords : 2^H<2^w := Nat.pow_lt_pow_right (by decide) (by omega)
  have hhost : 2*(2^v)^2+3<2^w := by
    have hp : 2^(2*v+4)≤2^w := Nat.pow_le_pow_right (by decide) (by omega)
    have he : 2^(2*v+4)=16*(2^v)^2 := by
      rw [pow_add, Nat.mul_comm 2 v, pow_mul]; norm_num; ring
    rw [he] at hp
    have hpos := Nat.one_le_pow v 2 (by decide)
    nlinarith only [hp,hpos]
  have hnonneg := Nat.zero_le (c*(2*R+H+1)^12)
  have hroom (s : String) (hs : s∈buffers) :
      c*(2*R+H+1)^12+3*R*R+6*R+10≤extent s := room s hs
  refine ⟨hN,hH,hs,ha,hc,positive,ht.trans hv,hhost,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (by omega : c*(N+H+j+1)^12+1≤w).trans_lt wlt
  · exact (by omega : Lax455465Proofs.RamVirtualConstants.allowance p≤w).trans_lt wlt
  · rw [hsize]
    exact (by nlinarith only [hNN,hNR,hbase] : 2+3*(N*N)+6*N+3≤w).trans_lt wlt
  · exact (by omega : m+j+limit+4+14+10≤w).trans_lt wlt
  · exact input_words j H (2^w) state a (by omega) (by omega) (by omega) hwords hs ha hc
  · have h := hroom "lp.word" (by simp [buffers]); rw [hsize]; nlinarith only [h,hNN,hNR,hnonneg]
  · have h := hroom "vm.input" (by simp [buffers]); rw [hsize]; nlinarith only [h,hNN,hNR,hnonneg]
  · have h := hroom "vm.addresses" (by simp [buffers]); omega
  · have h := hroom "vm.values" (by simp [buffers]); omega
  · have h := hroom "vm.output" (by simp [buffers]); omega
  · have h := hroom "round.shape" (by simp [buffers]); nlinarith only [h,hNN,hnonneg]
  · have h := hroom "round.center" (by simp [buffers]); omega

end Lax263307Proofs.NativeRoundedResources
