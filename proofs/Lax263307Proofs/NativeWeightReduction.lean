import Lax263307.IndependentSetEncoding
import Lax263307.WeightRounding
import Lax808846.Ram
import Lax263307Proofs.NativeMultiplicities
import Lax455465Proofs.RamEmitWords
import Lax109476Proofs.RamAutomaticLayout

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeWeightReduction

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307Proofs.NativeFrontend
open Lax263307.WeightedIndependentSet Lax263307.WeightRounding

def adjacency {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : List ℕ :=
  (List.ofFn fun u => List.ofFn fun v => if G.Adj u v then 1 else 0).flatten

def prepare : Com := .seq readInput (.seq NativeMaximum.command
  (.seq NativeMultiplicities.readAccuracy NativeMultiplicities.command))

def emit : Com := .seq (.assign "emit.count" (.var "input.n"))
  (Lax455465Proofs.RamEmitWords.command "copy.counts" 1)

def command : Com := .seq prepare emit

theorem adjacency_length {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (adjacency G).length=n*n := by
  simp [adjacency,List.length_flatten,List.sum_ofFn,Finset.sum_const]

theorem input_words {n : ℕ} (M : ℕ) (hM : 1≤M) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Fin n → ℚ) (ε : ℚ) (hw : ∀ v,(w v).num.natAbs≤M ∧ (w v).den≤M)
    (hε : ε.num.natAbs≤M ∧ ε.den≤M) : ∀ z∈tailInput G w ε,z≤M := by
  have hr (q : ℚ) (hq : q.num.natAbs≤M ∧ q.den≤M) : ∀ z∈encodeRational q,z≤M := by
    intro z hz
    simp only [encodeRational,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl
    · split_ifs <;> omega
    · exact hq.1
    · exact hq.2
  intro z hz
  simp only [tailInput,encodeParameters,List.mem_append] at hz
  rcases hz with hgraph | hweights | hacc
  · obtain ⟨row,hrow,hz⟩ := List.mem_flatten.mp hgraph
    obtain ⟨u,rfl⟩ := List.mem_ofFn.mp hrow
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hz
    split_ifs <;> omega
  · obtain ⟨q,hq,hz⟩ := List.mem_flatMap.mp hweights
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hq
    exact hr _ (hw v) z hz
  · exact hr _ hε z hacc

theorem prepare_spec {n : ℕ} (B M : ℕ) (hM : 1≤M) (hn : n≤M)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : Fin n → ℚ) (ε : ℚ) (hεpos : 0<ε)
    (hw : ∀ v,(w v).num.natAbs≤M ∧ (w v).den≤M) (hε : ε.num.natAbs≤M ∧ ε.den≤M)
    (hB : 2*M^4+3<B) (hsize : n*n+3*n+3<B) :
    Spec B (fun σ => σ.inp=encodeInput G w ε ∧ n*n+3*n+3≤(σ.arrs "input.data").length ∧
      n≤(σ.arrs "copy.counts").length) prepare
      (fun σ τ => Prefix (List.ofFn (copies (fun v => max (w v) 0) ε)) "copy.counts" τ ∧
        τ.vars "input.n"=n ∧ τ.out=σ.out ∧ Prefix (tailInput G w ε) "input.data" τ)
      (12*(n*n+3*n+3)+110*n+78) := by
  let qs := List.ofFn w
  let a := NativeMaximum.maximum qs
  have hqs : qs.length=n := List.length_ofFn
  have hp2 : M^2≤M^4 := Nat.pow_le_pow_right hM (by omega)
  have hp1 : M≤M^4 := by simpa using Nat.pow_le_pow_right hM (by omega : 1≤4)
  have hMB : M<B := by omega
  have hB2 : 2*M^2+3<B := by omega
  have hwords : ∀ q∈qs,q.num.natAbs≤M ∧ q.den≤M := by
    intro q hq
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hq
    exact hw v
  have hmax := NativeMaximum.maximum_bounds M hM qs hwords
  have htail : tailInput G w ε = adjacency G++qs.flatMap encodeRational++encodeRational ε := by
    simp only [tailInput,adjacency,encodeParameters,List.append_assoc,qs]
  have hfront := adjacency_length G
  rintro σ ⟨hinp,hroom,hcountsroom⟩
  obtain ⟨ν,r1,p1⟩ := read_input_spec B n (tailInput G w ε) hsize (tail_length G w ε)
    (fun z hz => (input_words M hM G w ε hw hε z hz).trans_lt hMB) σ
    ⟨by simpa only [encodeInput,tailInput,List.singleton_append,List.cons_append,List.nil_append,List.append_assoc] using hinp,
      by rwa [tail_length]⟩
  obtain ⟨μ,r2,p2⟩ := NativeMaximum.command_spec B M (adjacency G) (encodeRational ε) qs hM hB2
    (by rwa [hfront,hqs]) hwords ν ⟨by simpa only [htail] using p1.2.2.2.2.2,
      p1.2.1.trans hfront.symm,p1.1.trans hqs.symm⟩
  have r12 := r1.seq r2
  have hpμ : Prefix (adjacency G++qs.flatMap encodeRational++encodeRational ε) "input.data" μ := by
    simpa only [Prefix,r2.frame_arr "input.data" (by decide),htail] using p1.2.2.2.2.2
  have hbaseμ : μ.vars "input.matrixLength"=(adjacency G).length :=
    (r2.frame_var "input.matrixLength" (by decide)).trans (p1.2.1.trans hfront.symm)
  have hweightμ : μ.vars "input.weightLength"=3*qs.length :=
    (r2.frame_var "input.weightLength" (by decide)).trans (by simpa only [hqs] using p1.2.2.1)
  obtain ⟨ξ,r3,p3⟩ := NativeMultiplicities.read_accuracy_spec B (adjacency G) qs ε hεpos
    (by rwa [hfront,hqs]) (hε.1.trans_lt hMB) (hε.2.trans_lt hMB) μ ⟨hpμ,hbaseμ,hweightμ⟩
  have r123 := r1.seq (r2.seq r3)
  have hpξ : Prefix (adjacency G++qs.flatMap encodeRational++encodeRational ε) "input.data" ξ := by
    simpa only [Prefix,r3.frame_arr "input.data" (by decide)] using hpμ
  have hbaseξ := (r3.frame_var "input.matrixLength" (by decide)).trans hbaseμ
  have hnξ : ξ.vars "input.n"=qs.length :=
    (r3.frame_var "input.n" (by decide)).trans ((r2.frame_var "input.n" (by decide)).trans (p1.1.trans hqs.symm))
  have hmaxnξ : ξ.vars "maximum.n"=a.1 := (r3.frame_var "maximum.n" (by decide)).trans p2.1
  have hmaxdξ : ξ.vars "maximum.d"=a.2 := (r3.frame_var "maximum.d" (by decide)).trans p2.2
  have hcountsξ : qs.length≤(ξ.arrs "copy.counts").length := by
    rw [Lax455465Proofs.RamFrames.run_array_length r123,hqs]
    exact hcountsroom
  obtain ⟨τ,r4,p4⟩ := NativeMultiplicities.command_spec B M ε.num.natAbs ε.den a.1 a.2
    (adjacency G) (encodeRational ε) qs hM hB (by rwa [hqs]) hε.1 hε.2 hmax.1 hmax.2.1
    (by rwa [hfront,hqs]) hwords ξ ⟨hpξ,hbaseξ,hnξ,p3.1,p3.2,hmaxnξ,hmaxdξ,hcountsξ⟩
  have rtotal := r1.seq (r2.seq (r3.seq r4))
  refine ⟨τ,rtotal.mono (by simp only [tail_length,hqs]; omega),?_,?_,?_,?_⟩
  · have heq : NativeMultiplicities.counts n ε.num.natAbs ε.den a.1 a.2 qs =
        List.ofFn (copies (fun v => max (w v) 0) ε) := NativeMultiplicities.counts_correct w ε hεpos
    rw [hqs] at p4
    rw [heq] at p4
    exact p4
  · exact (r4.frame_var "input.n" (by decide)).trans (hnξ.trans hqs)
  · exact rtotal.out_eq (by decide)
  · have rr := r2.seq (r3.seq r4)
    simpa only [Prefix,rr.frame_arr "input.data" (by decide)] using p1.2.2.2.2.2


def cost (n : ℕ) : ℕ := 12*(n*n+3*n+3)+123*n+86


open Lax109476Proofs

def layout := RamAutomaticLayout.layout command
def program : Lax808846.Ram.Program := Lax808846Proofs.Compile.compileProgram layout command


end Lax263307Proofs.NativeWeightReduction
