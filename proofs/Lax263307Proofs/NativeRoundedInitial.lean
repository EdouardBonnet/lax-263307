import Lax263307Proofs.NativeIntegerTable
import Lax263307Proofs.NativeInitialCoordinates
import Lax263307Proofs.NativeRoundedState

set_option maxHeartbeats 800000

namespace Lax263307Proofs.NativeRoundedInitial

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 RoundedOracleSearch NativeRoundedQuery

def copy (target : String) (count : Expr) : Com :=
  .seq (.assign "fill.length" count)
    (.seq (.assign "slice.start" (.lit 0)) (NativeSlice.command "lp.input" target))

theorem copy_spec (B n : ℕ) (target : String) (xs : List ℕ) (count : Expr)
    (hne : "lp.input"≠target) (hB : xs.length+2<B) (hv : ∀ z∈xs,z<B)
    (hcount : ∀ σ,σ.vars "vec.n"=n → count.evalB B σ=some xs.length) :
    Spec B (fun σ => σ.vars "vec.n"=n ∧ Prefix xs "lp.input" σ ∧ xs.length≤(σ.arrs target).length)
      (copy target count) (fun _ τ => τ.vars "vec.n"=n ∧ Prefix xs target τ)
      (16*xs.length+count.size+9) := by
  rintro σ ⟨hn,hp,hroom⟩
  let ν := σ.setVar "fill.length" xs.length
  have r1 : Run B (.assign "fill.length" count) σ ν (count.size+1) :=
    (Run.assign (hcount σ hn)).mono (by omega)
  let μ := ν.setVar "slice.start" 0
  have r2 : Run B (.assign "slice.start" (.lit 0)) ν μ 2 := Run.assign (evalB_lit (show 0<B by omega))
  obtain ⟨τ,r3,p3⟩ := NativeSlice.command_spec B "lp.input" target [] xs [] hne
    (by simpa only [List.length_nil,Nat.zero_add] using (show xs.length+1<B by omega)) hv μ
    ⟨⟨by simpa only [List.nil_append,List.append_nil,Prefix,(r1.seq r2).frame_arr "lp.input" (by simp [Com.warrs])] using hp,
      by simp [μ]⟩,
      by simp [μ,ν],by simpa only [RamFrames.run_array_length (r1.seq r2)] using hroom⟩
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),
    ((r1.seq (r2.seq r3)).frame_var "vec.n" (by simp [copy,NativeSlice.command,NativeTabulate.command,
      NativeTabulate.append,NativeSlice.read,RamWordBuffer.append,Com.wvars])).trans hn,p3.2⟩

theorem shape_words (n : ℕ) :
    NativeRationalTabulate.words (NativeInitialCoordinates.values n)=shape ((1,0) : State n) := by
  have hf := NativeMatrixOrder.flatten n (1 : Matrix (Fin n) (Fin n) ℚ)
  rw [NativeRationalTabulate.words,NativeInitialCoordinates.values,hf]
  simp only [shape,encodeVector,List.flatMap_def,List.map_flatten,List.flatten_flatten,
    List.map_map,Function.comp_def,List.map_ofFn]

theorem center_words (n : ℕ) :
    NativeRationalTabulate.words (List.replicate n (0 : ℚ))=center ((1,0) : State n) := by
  change (List.replicate n (0 : ℚ)).flatMap encodeRational=(List.ofFn (fun _ : Fin n => (0 : ℚ))).flatMap encodeRational
  rw [List.ofFn_const]

theorem initial_words_bound (B n : ℕ) (hB : 1<B) :
    (∀ z∈shape ((1,0) : State n),z<B) ∧ (∀ z∈center ((1,0) : State n),z<B) := by
  constructor
  · rw [←shape_words]
    intro z hz
    obtain ⟨q,hq,hz⟩ := List.mem_flatMap.mp hz
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    simp only [Matrix.one_apply] at hz
    split_ifs at hz <;> simp [encodeRational] at hz <;> omega
  · rw [←center_words]
    intro z hz
    obtain ⟨q,hq,hz⟩ := List.mem_flatMap.mp hz
    have hq0 : q=0 := (List.mem_replicate.mp hq).2
    subst q
    simp [encodeRational] at hz
    omega

def matrixTable : Com := NativeIntegerTable.command (.mul (.var "vec.n") (.var "vec.n")) NativeInitialCoordinates.read
def centerTable : Com := NativeIntegerTable.command (.var "vec.n") NativeInitialCoordinates.zeroRead
def matrixCopy : Com := copy "round.shape" (.mul (.lit 3) (.mul (.var "vec.n") (.var "vec.n")))
def centerCopy : Com := copy "round.center" (.mul (.lit 3) (.var "vec.n"))
def command : Com := .seq matrixTable (.seq matrixCopy (.seq centerTable
  (.seq centerCopy (.assign "round.i" (.lit 0)))))

theorem matrix_table_spec (B n : ℕ) (hB : 3*(n*n)+3*n+20<B) :
    Spec B (fun σ => σ.vars "vec.n"=n ∧ 3*(n*n)≤(σ.arrs "lp.input").length) matrixTable
      (fun _ τ => τ.vars "vec.n"=n ∧ Prefix (shape ((1,0) : State n)) "lp.input" τ ∧
        τ.vars "lp.length"=3*(n*n)) (57*(n*n)+12) := by
  have hlen : (NativeInitialCoordinates.values n).length=n*n := List.length_ofFn
  have hcount : ∀ σ,σ.vars "vec.n"=n →
      (Expr.mul (.var "vec.n") (.var "vec.n")).evalB B σ=some (NativeInitialCoordinates.values n).length := by
    intro σ hn
    rw [hlen]
    apply evalB_bin (op:=.mul)
    · rw [evalB_var_iff]; exact ⟨hn.symm,by omega⟩
    · rw [evalB_var_iff]; exact ⟨hn.symm,by omega⟩
    · change n*n<B
      omega
  have hh := NativeIntegerTable.command_spec B n 18 (NativeInitialCoordinates.values n)
    (.mul (.var "vec.n") (.var "vec.n")) NativeInitialCoordinates.read
    (by rw [hlen]; omega) hcount (by decide) (by decide) (by decide) (by decide)
    (fun i hi => NativeInitialCoordinates.read_spec B n i hi (by omega))
  simpa only [hlen,shape_words,Expr.size,Nat.add_zero,Nat.reduceAdd,matrixTable] using hh

theorem center_table_spec (B n : ℕ) (hB : 3*n+2<B) :
    Spec B (fun σ => σ.vars "vec.n"=n ∧ 3*n≤(σ.arrs "lp.input").length) centerTable
      (fun _ τ => τ.vars "vec.n"=n ∧ Prefix (center ((1,0) : State n)) "lp.input" τ ∧
        τ.vars "lp.length"=3*n) (43*n+10) := by
  have hlen : (List.replicate n (0 : ℚ)).length=n := List.length_replicate
  have hh := NativeIntegerTable.command_spec B n 4 (List.replicate n (0 : ℚ)) (.var "vec.n")
    NativeInitialCoordinates.zeroRead (by rw [hlen]; exact hB)
    (by intro σ hn; rw [hlen,evalB_var_iff]; exact ⟨hn.symm,by omega⟩)
    (by decide) (by decide) (by decide) (by decide)
    (fun i hi => by
      rintro σ ⟨hn,_⟩
      simpa only [List.getElem_replicate] using NativeInitialCoordinates.zero_read_spec B n (by omega) σ hn)
  simpa only [hlen,center_words,Expr.size,Nat.add_zero,Nat.reduceAdd,centerTable] using hh

theorem matrix_copy_spec (B n : ℕ) (hB : 3*(n*n)+3*n+20<B) :
    Spec B (fun σ => σ.vars "vec.n"=n ∧ Prefix (shape ((1,0) : State n)) "lp.input" σ ∧
      3*(n*n)≤(σ.arrs "round.shape").length) matrixCopy
      (fun _ τ => τ.vars "vec.n"=n ∧ Prefix (shape ((1,0) : State n)) "round.shape" τ)
      (48*(n*n)+14) := by
  have hlen := shape_length ((1,0) : State n)
  have hc : ∀ σ,σ.vars "vec.n"=n →
      (Expr.mul (.lit 3) (.mul (.var "vec.n") (.var "vec.n"))).evalB B σ=some (shape ((1,0) : State n)).length := by
    intro σ hn
    rw [hlen]
    apply evalB_bin (op:=.mul) (evalB_lit (show 3<B by omega))
    · apply evalB_bin (op:=.mul)
      · rw [evalB_var_iff]; exact ⟨hn.symm,by omega⟩
      · rw [evalB_var_iff]; exact ⟨hn.symm,by omega⟩
      · change n*n<B
        omega
    · change 3*(n*n)<B
      omega
  have hh := copy_spec B n "round.shape" (shape ((1,0) : State n))
    (.mul (.lit 3) (.mul (.var "vec.n") (.var "vec.n"))) (by decide)
    (by rw [hlen]; omega) (initial_words_bound B n (by omega)).1 hc
  convert hh using 1 <;> simp only [hlen,Expr.size,Nat.reduceAdd,matrixCopy] <;> ring

theorem center_copy_spec (B n : ℕ) (hB : 3*n+3<B) :
    Spec B (fun σ => σ.vars "vec.n"=n ∧ Prefix (center ((1,0) : State n)) "lp.input" σ ∧
      3*n≤(σ.arrs "round.center").length) centerCopy
      (fun _ τ => τ.vars "vec.n"=n ∧ Prefix (center ((1,0) : State n)) "round.center" τ)
      (48*n+12) := by
  have hlen : (center ((1,0) : State n)).length=3*n := vector_length _
  have hc : ∀ σ,σ.vars "vec.n"=n →
      (Expr.mul (.lit 3) (.var "vec.n")).evalB B σ=some (center ((1,0) : State n)).length := by
    intro σ hn
    rw [hlen]
    apply evalB_bin (op:=.mul) (evalB_lit (show 3<B by omega))
    · rw [evalB_var_iff]; exact ⟨hn.symm,by omega⟩
    · change 3*n<B
      omega
  have hh := copy_spec B n "round.center" (center ((1,0) : State n))
    (.mul (.lit 3) (.var "vec.n")) (by decide)
    (by rw [hlen]; omega) (initial_words_bound B n (by omega)).2 hc
  convert hh using 1 <;> simp only [hlen,Expr.size,Nat.reduceAdd,centerCopy] <;> ring

/-- Build the initial identity shape and zero center by actual RAM
loops, and initialize the numeric rounded-update index. -/
theorem command_spec (B n : ℕ) (hB : 3*(n*n)+3*n+20<B) :
    Spec B (fun σ => σ.vars "vec.n"=n ∧ 3*(n*n)+3*n≤(σ.arrs "lp.input").length ∧
      3*(n*n)≤(σ.arrs "round.shape").length ∧ 3*n≤(σ.arrs "round.center").length) command
      (fun _ τ => τ.vars "vec.n"=n ∧ Prefix (shape ((1,0) : State n)) "round.shape" τ ∧
        Prefix (center ((1,0) : State n)) "round.center" τ ∧ τ.vars "round.i"=0)
      (105*(n*n)+91*n+50) := by
  rintro σ ⟨hn,hinput,hshape,hcenter⟩
  obtain ⟨ν,r1,p1⟩ := matrix_table_spec B n hB σ ⟨hn,by omega⟩
  obtain ⟨μ,r2,p2⟩ := matrix_copy_spec B n hB ν
    ⟨p1.1,p1.2.1,by rw [RamFrames.run_array_length r1]; exact hshape⟩
  obtain ⟨ρ,r3,p3⟩ := center_table_spec B n (by omega) μ
    ⟨p2.1,by rw [RamFrames.run_array_length r2,RamFrames.run_array_length r1]; omega⟩
  obtain ⟨υ,r4,p4⟩ := center_copy_spec B n (by omega) ρ
    ⟨p3.1,p3.2.1,by rw [RamFrames.run_array_length r3,RamFrames.run_array_length r2,
      RamFrames.run_array_length r1]; exact hcenter⟩
  let τ := υ.setVar "round.i" 0
  have r5 : Run B (.assign "round.i" (.lit 0)) υ τ 2 := Run.assign (evalB_lit (show 0<B by omega))
  refine ⟨τ,(r1.seq (r2.seq (r3.seq (r4.seq r5)))).mono (by nlinarith only []),
    (r5.frame_var "vec.n" (by decide)).trans p4.1,?_,?_,by rfl⟩
  · simpa only [Prefix,(r3.seq (r4.seq r5)).frame_arr "round.shape" (by decide)] using p2.2
  · simpa only [Prefix,r5.frame_arr "round.center" (by decide)] using p4.2

end Lax263307Proofs.NativeRoundedInitial
