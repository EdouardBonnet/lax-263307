import Lax263307Proofs.NativeRoundedQuery
import Lax263307Proofs.NativeMatrixOrder
import Lax263307Proofs.NativeSlice

namespace Lax263307Proofs.NativeRoundedState

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 RoundedOracleSearch
open NativeRoundedQuery

theorem encoded_output {n : ℕ} (state : State n) :
    Lax263307.NativeRoundedStep.encodeOutput state=shape state++center state := by
  have hflat : List.ofFn (fun i : Fin (n*n) => state.1 i.divNat i.modNat)=
      (List.ofFn fun i => List.ofFn (state.1 i)).flatten := by
    calc
      _=List.ofFn (fun i : Fin (n*n) => state.1 (NativeBlowUp.row i) (NativeBlowUp.col i)) := by
        apply congrArg List.ofFn
        funext i
        congr 1 <;> apply Fin.ext <;> rfl
      _=_ := NativeMatrixOrder.flatten n state.1
  have he : ((List.ofFn fun i => List.ofFn (state.1 i)).flatten).flatMap encodeRational=shape state := by
    simp only [shape,encodeVector,List.flatMap_def,List.map_flatten,List.flatten_flatten,
      List.map_map,Function.comp_def,List.map_ofFn]
  simp only [Lax263307.NativeRoundedStep.encodeOutput,hflat,he,center]

def shapeSetup : Com := .seq (.assign "fill.length" (.mul (.lit 3) (.mul (.var "vec.n") (.var "vec.n"))))
  (.assign "slice.start" (.lit 0))

def centerSetup : Com := .seq (.assign "fill.length" (.mul (.lit 3) (.var "vec.n")))
  (.assign "slice.start" (.mul (.lit 3) (.mul (.var "vec.n") (.var "vec.n"))))

def command : Com := .seq shapeSetup (.seq (NativeSlice.command "vm.output" "round.shape")
  (.seq centerSetup (NativeSlice.command "vm.output" "round.center")))

theorem shape_setup_spec (B n : ℕ) (hB : 3*(n*n)+3*n+3<B) :
    Spec B (fun σ => σ.vars "vec.n"=n) shapeSetup
      (fun _ τ => τ.vars "vec.n"=n ∧ τ.vars "fill.length"=3*(n*n) ∧ τ.vars "slice.start"=0) 8 := by
  intro σ hs
  run_vcg
  all_goals simp_all [Env.setVar] <;> omega

theorem center_setup_spec (B n : ℕ) (hB : 3*(n*n)+3*n+3<B) :
    Spec B (fun σ => σ.vars "vec.n"=n) centerSetup
      (fun _ τ => τ.vars "vec.n"=n ∧ τ.vars "fill.length"=3*n ∧ τ.vars "slice.start"=3*(n*n)) 10 := by
  intro σ hs
  run_vcg
  all_goals simp_all [Env.setVar] <;> omega

/-- Decode the rounded subroutine's actual output into persistent
shape and center buffers, preserving the node dimension. -/
theorem command_spec {n : ℕ} (B : ℕ) (state : State n)
    (hB : 3*(n*n)+3*n+3<B) (hv : ∀ z∈Lax263307.NativeRoundedStep.encodeOutput state,z<B) :
    Spec B (fun σ => Prefix (Lax263307.NativeRoundedStep.encodeOutput state) "vm.output" σ ∧
      σ.vars "vec.n"=n ∧ 3*(n*n)≤(σ.arrs "round.shape").length ∧ 3*n≤(σ.arrs "round.center").length)
      command (fun _ τ => Prefix (shape state) "round.shape" τ ∧ Prefix (center state) "round.center" τ ∧
        τ.vars "vec.n"=n) (48*(n*n)+48*n+30) := by
  have hA := shape_length state
  have hc : (center state).length=3*n := vector_length _
  rintro σ ⟨hp,hn,hroomA,hroomc⟩
  obtain ⟨ν,r1,p1⟩ := shape_setup_spec B n hB σ hn
  have hprefix : Prefix (shape state++center state) "vm.output" ν := by
    simpa only [encoded_output,Prefix,r1.frame_arr "vm.output" (by decide)] using hp
  obtain ⟨μ,r2,p2⟩ := NativeSlice.command_spec B "vm.output" "round.shape" [] (shape state) (center state) (by decide)
    (by rw [hA]; simp; omega) (fun z hz => hv z (by rw [encoded_output]; exact List.mem_append_left _ hz)) ν
    ⟨⟨by simpa only [List.nil_append] using hprefix,by simpa only [List.length_nil] using p1.2.2⟩,
      by simpa only [hA] using p1.2.1,by simpa only [hA,RamFrames.run_array_length r1] using hroomA⟩
  have hn2 := (r2.frame_var "vec.n" (by decide)).trans p1.1
  obtain ⟨ρ,r3,p3⟩ := center_setup_spec B n hB μ hn2
  obtain ⟨τ,r4,p4⟩ := NativeSlice.command_spec B "vm.output" "round.center" (shape state) (center state) [] (by decide)
    (by rw [hA,hc]; omega) (fun z hz => hv z (by rw [encoded_output]; exact List.mem_append_right _ hz)) ρ
    ⟨⟨by simpa only [List.append_nil,Prefix,(r1.seq (r2.seq r3)).frame_arr "vm.output" (by decide),encoded_output] using hp,
      by simpa only [hA] using p3.2.2⟩,
      by simpa only [hc] using p3.2.1,
      by simpa only [hc,RamFrames.run_array_length r3,RamFrames.run_array_length r2,RamFrames.run_array_length r1] using hroomc⟩
  exact ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono (by rw [hA,hc]; nlinarith only []),
    by simpa only [Prefix,(r3.seq r4).frame_arr "round.shape" (by decide)] using p2.2,p4.2,
    (r4.frame_var "vec.n" (by decide)).trans p3.1⟩

end Lax263307Proofs.NativeRoundedState
