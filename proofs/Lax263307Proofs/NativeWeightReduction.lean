import Lax263307.NativeWeightReduction
import Lax263307Proofs.NativeMultiplicities
import Lax455465Proofs.RamEmitWords
import Lax109476Proofs.RamAutomaticLayout

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeWeightReduction

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
        τ.vars "input.n"=n ∧ τ.out=σ.out) (12*(n*n+3*n+3)+110*n+78) := by
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
  refine ⟨τ,rtotal.mono (by simp only [tail_length,hqs]; omega),?_,?_,?_⟩
  · have heq : NativeMultiplicities.counts n ε.num.natAbs ε.den a.1 a.2 qs =
        List.ofFn (copies (fun v => max (w v) 0) ε) := NativeMultiplicities.counts_correct w ε hεpos
    rw [hqs] at p4
    rw [heq] at p4
    exact p4
  · exact (r4.frame_var "input.n" (by decide)).trans (hnξ.trans hqs)
  · exact rtotal.out_eq (by decide)


theorem output_words {n : ℕ} (B M : ℕ) (hM : 1≤M) (hn : n≤M)
    (w : Fin n → ℚ) (ε : ℚ) (hεpos : 0<ε)
    (hw : ∀ v,(w v).num.natAbs≤M ∧ (w v).den≤M) (hε : ε.num.natAbs≤M ∧ ε.den≤M)
    (hB : 2*M^4+3<B) : ∀ z∈List.ofFn (copies (fun v => max (w v) 0) ε),z<B := by
  let qs := List.ofFn w
  let a := NativeMaximum.maximum qs
  have hwords : ∀ q∈qs,q.num.natAbs≤M ∧ q.den≤M := by
    intro q hq
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hq
    exact hw v
  have hmax := NativeMaximum.maximum_bounds M hM qs hwords
  have heq : NativeMultiplicities.counts n ε.num.natAbs ε.den a.1 a.2 qs =
      List.ofFn (copies (fun v => max (w v) 0) ε) := NativeMultiplicities.counts_correct w ε hεpos
  rw [← heq]
  intro z hz
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hz
  have hq' := hwords q hq
  have hc : clippedNumerator q≤M := by unfold clippedNumerator; split_ifs <;> omega
  have hb := NativeMultiplicities.product_bounds B M n (clippedNumerator q) q.den ε.num.natAbs ε.den a.1 a.2
    hM hB hn hc hq'.2 hε.1 hε.2 hmax.1 hmax.2.1
  rcases hb with ⟨_,_,_,_,_,_,_,_,_,_,_,hprod,_,_⟩
  exact (Nat.div_le_self _ _).trans_lt hprod

def cost (n : ℕ) : ℕ := 12*(n*n+3*n+3)+123*n+86

theorem command_spec {n : ℕ} (B M : ℕ) (hM : 1≤M) (hn : n≤M)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : Fin n → ℚ) (ε : ℚ) (hεpos : 0<ε)
    (hw : ∀ v,(w v).num.natAbs≤M ∧ (w v).den≤M) (hε : ε.num.natAbs≤M ∧ ε.den≤M)
    (hB : 2*M^4+3<B) (hsize : n*n+3*n+3<B) :
    Spec B (fun σ => σ.inp=encodeInput G w ε ∧ n*n+3*n+3≤(σ.arrs "input.data").length ∧
      n≤(σ.arrs "copy.counts").length) command
      (fun σ τ => τ.out=σ.out++List.ofFn (copies (fun v => max (w v) 0) ε)) (cost n) := by
  have hnB : n<B := by omega
  have h1 : 1<B := by omega
  let xs := List.ofFn (copies (fun v => max (w v) 0) ε)
  have hlen : xs.length=n := List.length_ofFn
  rintro σ hσ
  obtain ⟨ν,r1,hp,hnum,hout⟩ := prepare_spec B M hM hn G w ε hεpos hw hε hB hsize σ hσ
  let μ := ν.setVar "emit.count" n
  have r2 : Run B (.assign "emit.count" (.var "input.n")) ν μ 2 := Run.assign (by
    rw [evalB_var_iff]; exact ⟨hnum.symm,hnum ▸ hnB⟩)
  have hdata : Lax455465Proofs.RamEmitWords.Data "copy.counts" 1 xs μ := by
    simpa only [Lax455465Proofs.RamEmitWords.Data,Prefix,one_mul,μ,arrs_setVar,xs] using hp
  obtain ⟨τ,r3,p3⟩ := Lax455465Proofs.RamEmitWords.command_spec B "copy.counts" 1 xs σ.out h1 h1
    (by simpa only [one_mul,hlen] using hnB) (by rwa [hlen])
    (output_words B M hM hn w ε hεpos hw hε hB) μ
    ⟨hdata,by simp [μ,hlen],hout⟩
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by simp only [cost,hlen]; omega),p3⟩


open Lax109476Proofs

def layout := RamAutomaticLayout.layout command
def program : Lax808846.Ram.Program := Lax808846Proofs.Compile.compileProgram layout command

theorem compiled_runs_to {n : ℕ} (v width M : ℕ) (hv : 0<v)
    (hwidth : v+RamTransfer.layoutAllowance layout≤width) (hM : 1≤M) (hn : n≤M)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : Fin n → ℚ) (ε : ℚ) (hεpos : 0<ε)
    (hw : ∀ i,(w i).num.natAbs≤M ∧ (w i).den≤M) (hε : ε.num.natAbs≤M ∧ ε.den≤M)
    (hB : 2*M^4+3<2^v) (hsize : n*n+3*n+3<2^v)
    (hinput : ∀ z∈encodeInput G w ε,z<2^v) :
    ∃ t≤10*cost n+1,Lax808846.Ram.RunsTo width program (encodeInput G w ε)
      (List.ofFn (copies (fun i => max (w i) 0) ε)) t := by
  obtain ⟨τ,hr,hout⟩ := command_spec (2^v) M hM hn G w ε hεpos hw hε hB hsize
    (initEnv (fun _ => n*n+3*n+3) (encodeInput G w ε))
    ⟨rfl,by simp [initEnv],by simp [initEnv]; omega⟩
  obtain ⟨K,hK,hbs⟩ := hr
  obtain ⟨t,ht,hrun⟩ := Lax808846Proofs.Simulation.compileProgram_runsTo
    (RamTransfer.layout_fits hv hwidth) (RamAutomaticLayout.layout_ok command) hinput hbs
  refine ⟨t,ht.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 10 hK) 1),?_⟩
  simpa only [program,layout,hout,initEnv,List.nil_append] using hrun

/--
---
conclusion: Lax263307.NativeWeightReduction.exists_program
---
The compiled command consumes the actual encoded input and emits its computed
multiplicity buffer. A single explicit magnitude exponent bounds all integer
products, source indices, and input words. Layout allowance and instruction
counts fit one fixed quadratic polynomial, for every larger word width.
-/
theorem exists_program : ∃ p : Lax808846.Ram.Program, ∃ c : ℕ, 0<c ∧
    ∀ (n h : ℕ), 1≤h → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (w : Fin n → ℚ) (ε : ℚ), 0<ε →
      (∀ i,(w i).num.natAbs≤2^h ∧ (w i).den≤2^h) →
      ε.num.natAbs≤2^h → ε.den≤2^h →
      ∀ width : ℕ,c*(n+h+1)^2≤width →
      ∃ t≤c*(n+h+1)^2,Lax808846.Ram.RunsTo width p (encodeInput G w ε)
        (List.ofFn (copies (fun i => max (w i) 0) ε)) t := by
  let C := 10000+RamTransfer.layoutAllowance layout
  refine ⟨program,C,by dsimp [C]; omega,?_⟩
  intro n h hh G _ w ε hεpos hw hεn hεd width hwidth
  let X := n+h+1
  let E := n+h+2
  let M := 2^E
  let v := 4*E+(n*n+3*n+3)+10
  have hX : 1≤X := by dsimp [X]; omega
  have hnX : n≤X := by dsimp [X]; omega
  have hhX : h≤X := by dsimp [X]; omega
  have hXX : X≤X^2 := le_self_pow hX (by omega)
  have h1X : 1≤X^2 := Nat.one_le_pow 2 X (by omega)
  have hnnX : n*n≤X^2 := by simpa only [pow_two] using Nat.mul_le_mul hnX hnX
  have hvbound : v≤40*X^2 := by
    dsimp only [v,E]
    nlinarith only [hnnX,hnX,hhX,hXX,h1X]
  have hwv : v+RamTransfer.layoutAllowance layout≤width := by
    change C*X^2≤width at hwidth
    have ha := Nat.mul_le_mul_left (RamTransfer.layoutAllowance layout) h1X
    dsimp only [C] at hwidth
    nlinarith only [hwidth,hvbound,ha]
  have hv : 0<v := by dsimp [v]; omega
  have hM : 1≤M := Nat.one_le_pow E 2 (by omega)
  have hnM : n≤M := (show n≤E by dsimp [E]; omega).trans Nat.lt_two_pow_self.le
  have hhM : 2^h≤M := Nat.pow_le_pow_right (by omega) (by dsimp [E]; omega)
  have hM4 : M^4=2^(4*E) := by dsimp [M]; rw [←pow_mul,Nat.mul_comm]
  have hpow : 2^(4*E+3)=8*M^4 := by rw [pow_add,←hM4]; norm_num; omega
  have hMp : 1≤M^4 := Nat.one_le_pow 4 M (by omega)
  have hguard : 2*M^4+3<2^v := by
    apply lt_of_lt_of_le (b:=2^(4*E+3))
    · rw [hpow]
      omega
    · apply Nat.pow_le_pow_right (by omega)
      dsimp [v]
      omega
  have hsize : n*n+3*n+3<2^v :=
    (show n*n+3*n+3<v by dsimp [v]; omega).trans Nat.lt_two_pow_self
  have hMB : M<2^v := Nat.pow_lt_pow_right (by omega) (by dsimp [v]; omega)
  have hinput : ∀ z∈encodeInput G w ε,z<2^v := by
    change ∀ z∈n::tailInput G w ε,z<2^v
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hnM.trans_lt hMB
    · exact (input_words M hM G w ε (fun i => ⟨(hw i).1.trans hhM,(hw i).2.trans hhM⟩)
        ⟨hεn.trans hhM,hεd.trans hhM⟩ z hz).trans_lt hMB
  obtain ⟨t,ht,hrun⟩ := compiled_runs_to v width M hv hwv hM hnM G w ε hεpos
    (fun i => ⟨(hw i).1.trans hhM,(hw i).2.trans hhM⟩) ⟨hεn.trans hhM,hεd.trans hhM⟩ hguard hsize hinput
  refine ⟨t,ht.trans ?_,hrun⟩
  change 10*cost n+1≤C*X^2
  have hcost : 10*cost n+1≤10000*X^2 := by
    dsimp only [cost]
    nlinarith only [hnnX,hnX,hXX,h1X]
  exact hcost.trans (Nat.mul_le_mul_right _ (by dsimp [C]; omega))

end Lax263307Proofs.NativeWeightReduction
