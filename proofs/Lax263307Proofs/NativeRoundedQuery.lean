import Lax263307Proofs.NativeQueryBlocks
import Lax263307.NativeRoundedStep

namespace Lax263307Proofs.NativeRoundedQuery

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 RoundedOracleSearch

def shape {n : ℕ} (state : State n) : List ℕ := (List.ofFn fun i => encodeVector (state.1 i)).flatten
def normal {n : ℕ} (a : Fin n → ℤ) : List ℕ := encodeVector (rationalNormal a)
def center {n : ℕ} (state : State n) : List ℕ := encodeVector state.2

theorem vector_length {n : ℕ} (v : Fin n → ℚ) : (encodeVector v).length=3*n := by
  simp [encodeVector,encodeRational,List.length_flatMap,List.sum_ofFn,Finset.sum_const] <;> ring

theorem shape_length {n : ℕ} (state : State n) : (shape state).length=3*(n*n) := by
  simp [shape,List.length_flatten,vector_length,List.sum_ofFn,Finset.sum_const] <;> ring

structure Data {n : ℕ} (k : ℕ) (state : State n) (a : Fin n → ℤ) (σ : Env) : Prop where
  order : σ.vars "vec.n"=n
  index : σ.vars "round.i"=k
  shape : Prefix (shape state) "round.shape" σ
  normal : Prefix (normal a) "round.normal" σ
  center : Prefix (center state) "round.center" σ
  room : (Lax263307.NativeRoundedStep.encodeInput k state a).length≤(σ.arrs "lp.word").length

theorem frame {B K n k : ℕ} {state : State n} {a : Fin n → ℤ} {c : Com} {σ τ : Env}
    (rr : Run B c σ τ K) (hd : Data k state a σ) (hn : "vec.n"∉c.wvars) (hi : "round.i"∉c.wvars)
    (hA : "round.shape"∉c.warrs) (ha : "round.normal"∉c.warrs) (hc : "round.center"∉c.warrs) : Data k state a τ := by
  refine ⟨(rr.frame_var _ hn).trans hd.order,(rr.frame_var _ hi).trans hd.index,?_,?_,?_,?_⟩
  · simpa only [Prefix,rr.frame_arr "round.shape" hA] using hd.shape
  · simpa only [Prefix,rr.frame_arr "round.normal" ha] using hd.normal
  · simpa only [Prefix,rr.frame_arr "round.center" hc] using hd.center
  · rw [RamFrames.run_array_length rr]; exact hd.room

def header : Com := .seq (.assign "lp.position" (.lit 0))
  (.seq (RamWordBuffer.append "lp.word" "lp.position" (.var "vec.n"))
    (RamWordBuffer.append "lp.word" "lp.position" (.var "round.i")))

theorem header_spec (B n k : ℕ) (hn : n<B) (hk : k<B) (hB : 4<B) :
    Spec B (fun σ => σ.vars "vec.n"=n ∧ σ.vars "round.i"=k ∧ 2≤(σ.arrs "lp.word").length)
      header (fun _ τ => Prefix [n,k] "lp.word" τ ∧ τ.vars "lp.position"=2) 16 := by
  rintro σ ⟨hnσ,hkσ,hroom⟩
  let ν := σ.setVar "lp.position" 0
  have r1 : Run B (.assign "lp.position" (.lit 0)) σ ν 2 := Run.assign (evalB_lit (show 0<B by omega))
  obtain ⟨μ,r2,p2⟩ := RamWordBuffer.append_spec B "lp.word" "lp.position" [] n (.var "vec.n") (by omega) (by simp; omega)
    ν ⟨by simp [Prefix],by simp [ν],by simp only [List.length_nil,ν,arrs_setVar]; omega,
      by rw [evalB_var_iff]; exact ⟨((r1.frame_var "vec.n" (by decide)).trans hnσ).symm,
        ((r1.frame_var "vec.n" (by decide)).trans hnσ) ▸ hn⟩⟩
  obtain ⟨τ,r3,p3⟩ := RamWordBuffer.append_spec B "lp.word" "lp.position" [n] k (.var "round.i") (by omega) (by simp; omega)
    μ ⟨p2.1,by simpa using p2.2,by rw [RamFrames.run_array_length r2]; simp only [List.length_singleton,ν,arrs_setVar]; omega,
      by rw [evalB_var_iff]; exact ⟨(((r1.seq r2).frame_var "round.i" (by decide)).trans hkσ).symm,
        (((r1.seq r2).frame_var "round.i" (by decide)).trans hkσ) ▸ hk⟩⟩
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by simp [Expr.size]),p3.1,by simpa using p3.2⟩

def command : Com := .seq header
  (.seq (NativeQueryBlocks.command "round.shape" (.mul (.lit 3) (.mul (.var "vec.n") (.var "vec.n"))))
    (.seq (NativeQueryBlocks.command "round.normal" (.mul (.lit 3) (.var "vec.n")))
      (NativeQueryBlocks.command "round.center" (.mul (.lit 3) (.var "vec.n")))))

/-- Construct the rounded update's raw query directly from its stored
shape, normal and center, without touching any recursion-stack cursor. -/
theorem command_spec {n : ℕ} (B k : ℕ) (state : State n) (a : Fin n → ℤ)
    (hB : (Lax263307.NativeRoundedStep.encodeInput k state a).length+3<B)
    (hv : ∀ z∈Lax263307.NativeRoundedStep.encodeInput k state a,z<B) :
    Spec B (Data k state a) command (fun _ τ => Data k state a τ ∧
      Prefix (Lax263307.NativeRoundedStep.encodeInput k state a) "lp.word" τ ∧
      τ.vars "lp.position"=(Lax263307.NativeRoundedStep.encodeInput k state a).length)
      (48*(n*n)+96*n+48) := by
  have hlen : (Lax263307.NativeRoundedStep.encodeInput k state a).length=2+3*(n*n)+6*n := by
    change ([n,k]++shape state++normal a++center state).length=2+3*(n*n)+6*n
    simp only [List.length_append,List.length_cons,List.length_nil,Nat.add_zero,shape_length,normal,center,vector_length]
    omega
  have hn : n<B := by rw [hlen] at hB; omega
  have hk : k<B := hv k (by simp [Lax263307.NativeRoundedStep.encodeInput])
  have hwords : ∀ z∈[n,k]++shape state++normal a++center state,z<B := hv
  have hsh := shape_length state
  have hno : (normal a).length=3*n := vector_length _
  have hce : (center state).length=3*n := vector_length _
  intro σ hd
  have hroom := hd.room
  obtain ⟨ν,r1,p1⟩ := header_spec B n k hn hk (by rw [hlen] at hB; omega) σ
    ⟨hd.order,hd.index,by rw [hlen] at hroom; omega⟩
  have hd1 := frame r1 hd (by decide) (by decide) (by decide) (by decide) (by decide)
  have emat : (Expr.mul (.lit 3) (.mul (.var "vec.n") (.var "vec.n"))).evalB B ν=some (shape state).length := by
    rw [hsh]
    apply evalB_bin (op:=.mul) (evalB_lit (show 3<B by rw [hlen] at hB; omega))
    · exact evalB_bin (op:=.mul)
        (by rw [evalB_var_iff]; exact ⟨hd1.order.symm,hd1.order ▸ hn⟩)
        (by rw [evalB_var_iff]; exact ⟨hd1.order.symm,hd1.order ▸ hn⟩)
        (by change n*n<B; rw [hlen] at hB; omega)
    · change 3*(n*n)<B
      rw [hlen] at hB
      omega
  obtain ⟨μ,r2,p2⟩ := NativeQueryBlocks.command_spec B "round.shape" _ [n,k] (shape state) (by decide)
    (by rw [hsh]; rw [hlen] at hB; simp; omega)
    (fun z hz => hwords z (by simp only [List.mem_append]; tauto)) ν
    ⟨hd1.shape,p1.1,by simpa using p1.2,emat,by rw [RamFrames.run_array_length r1]; rw [hlen] at hroom; simp [hsh]; omega⟩
  have hd2 := frame r2 hd1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have enormal : (Expr.mul (.lit 3) (.var "vec.n")).evalB B μ=some (normal a).length := by
    rw [hno]
    exact evalB_bin (op:=.mul) (evalB_lit (show 3<B by rw [hlen] at hB; omega))
      (by rw [evalB_var_iff]; exact ⟨hd2.order.symm,hd2.order ▸ hn⟩) (by change 3*n<B; rw [hlen] at hB; omega)
  obtain ⟨ρ,r3,p3⟩ := NativeQueryBlocks.command_spec B "round.normal" _ ([n,k]++shape state) (normal a) (by decide)
    (by rw [hno]; rw [hlen] at hB; simp [hsh]; omega)
    (fun z hz => hwords z (by simp only [List.mem_append]; tauto)) μ
    ⟨hd2.normal,p2.2.1,by simpa only [List.length_append] using p2.2.2,enormal,
      by rw [RamFrames.run_array_length r2,RamFrames.run_array_length r1]; rw [hlen] at hroom; simp [hsh,hno]; omega⟩
  have hd3 := frame r3 hd2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have ecenter : (Expr.mul (.lit 3) (.var "vec.n")).evalB B ρ=some (center state).length := by
    rw [hce]
    exact evalB_bin (op:=.mul) (evalB_lit (show 3<B by rw [hlen] at hB; omega))
      (by rw [evalB_var_iff]; exact ⟨hd3.order.symm,hd3.order ▸ hn⟩) (by change 3*n<B; rw [hlen] at hB; omega)
  obtain ⟨τ,r4,p4⟩ := NativeQueryBlocks.command_spec B "round.center" _ (([n,k]++shape state)++normal a) (center state) (by decide)
    (by rw [hce]; rw [hlen] at hB; simp [hsh,hno]; omega)
    (fun z hz => hwords z (by simp only [List.mem_append]; tauto)) ρ
    ⟨hd3.center,p3.2.1,by simpa only [List.length_append] using p3.2.2,ecenter,
      by rw [RamFrames.run_array_length r3,RamFrames.run_array_length r2,RamFrames.run_array_length r1]; rw [hlen] at hroom; simp [hsh,hno,hce]; omega⟩
  refine ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono ?_,frame r4 hd3 (by decide) (by decide) (by decide) (by decide) (by decide),?_,?_⟩
  · simp only [hsh,hno,hce,Expr.size]
    nlinarith only []
  · simpa only [Lax263307.NativeRoundedStep.encodeInput,shape,normal,center,List.append_assoc] using p4.2.1
  · simpa only [Lax263307.NativeRoundedStep.encodeInput,← List.append_assoc,List.length_append,
      shape,normal,center,Nat.add_assoc] using p4.2.2

end Lax263307Proofs.NativeRoundedQuery
