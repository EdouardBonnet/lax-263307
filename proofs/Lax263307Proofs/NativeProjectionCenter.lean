import Lax263307Proofs.NativeRoundedQuery
import Lax263307Proofs.NativeRationalBounds
import Lax263307Proofs.NativeScaleFraction
import Lax263307Proofs.NativeRationalRead
import Lax263307Proofs.NativeProgramCache
import Lax455465Proofs.RamVectorEncoding
import Lax263307.ProjectedOracle

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeProjectionCenter

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState Lax455465Proofs.RamRational
open Lax109476.RationalEncoding NativeSignedArithmetic

def Context {n : ℕ} (x : Fin n → ℚ) (σ : Env) : Prop :=
  σ.vars "vec.n"=n ∧ Prefix (encodeVector x) "round.center" σ

def Q {n : ℕ} (x : Fin n → ℚ) (σ : Env) : Prop := Context x σ ∧ σ.vars "scale.value"=4*n

theorem q_frame {B n t : ℕ} {x : Fin n → ℚ} {c : Com} {σ τ : Env} (rr : Run B c σ τ t)
    (hs : Q x σ) (hn : "vec.n"∉c.wvars) (hv : "scale.value"∉c.wvars)
    (ha : "round.center"∉c.warrs) : Q x τ := by
  refine ⟨⟨(rr.frame_var _ hn).trans hs.1.1,?_⟩,(rr.frame_var _ hv).trans hs.2⟩
  simpa only [Prefix,rr.frame_arr "round.center" ha] using hs.1.2

def setup : Com := .seq (.assign "scale.value" (.mul (.lit 4) (.var "vec.n")))
  (.assign "lp.position" (.lit 0))
def read : Com := .seq (.assign "read.cursor" (.mul (.lit 3) (.var "scale.i")))
  (.seq (NativeRationalRead.command "round.center") NativeScaleFraction.command)
def vector : Com := .seq setup (RamVectorEncoding.command "scale.i" "vec.n" read)
def command : Com := .seq vector (NativeProgramCache.copy "lp.word" "projection.center" "lp.position")

theorem setup_spec (B n : ℕ) (x : Fin n → ℚ) (hB : 4*n+5<B) :
    Spec B (Context x) setup (fun _ τ => Q x τ ∧ τ.vars "lp.position"=0) 6 := by
  intro σ hs
  run_vcg
  all_goals simp_all [Q,Context,Prefix,Env.setVar]
  all_goals omega

theorem read_spec (B M n : ℕ) (x : Fin n → ℚ) (i : ℕ) (hi : i<n)
    (hB : 2*M^2+3<B) (hshape : 4*n+5<B) (hscale : 4*n≤M) (hx : ∀ j,Bounded M (x j)) :
    Spec B (fun σ => Q x σ ∧ σ.vars "scale.i"=i) read
      (fun _ τ => Q x τ ∧ FractionOutput (Lax263307.ProjectedOracle.raw x ⟨i,hi⟩) τ)
      (36*M.size+41) := by
  let j : Fin n := ⟨i,hi⟩
  have hM : M<B := by have hp := (hx j).2; have hd := (x j).den_pos; nlinarith only [hB,hp,hd]
  rintro σ ⟨hs,hiσ⟩
  let ν := σ.setVar "read.cursor" (3*i)
  have r1 : Run B (.assign "read.cursor" (.mul (.lit 3) (.var "scale.i"))) σ ν 4 := Run.assign
    (evalB_bin (op:=.mul) (evalB_lit (show 3<B by omega))
      (by rw [evalB_var_iff]; exact ⟨hiσ.symm,hiσ ▸ (by omega)⟩) (by change 3*i<B; omega))
  obtain ⟨μ,r2,p2⟩ := NativeRationalRead.vector_entry_spec B "round.center" [] [] (List.ofFn x)
    i (by simpa only [List.length_ofFn] using hi) (by omega) (by simp; omega)
    (by simpa only [List.getElem_ofFn] using (hx j).1.trans_lt hM)
    (by simpa only [List.getElem_ofFn] using (hx j).2.trans_lt hM) ν
    ⟨by simpa only [List.nil_append,List.append_nil,Prefix,r1.frame_arr "round.center" (by decide),
      NativeRationalTabulate.words,encodeVector] using hs.1.2,by simp [ν]⟩
  have hqμ : FractionOutput (x j) μ := by simpa only [List.getElem_ofFn] using p2.1
  have hsμ := ((r1.seq r2).frame_var "scale.value" (by decide)).trans hs.2
  obtain ⟨τ,r3,p3⟩ := NativeScaleFraction.command_spec B M (4*n) (x j) hB hscale (hx j) μ ⟨hqμ,hsμ⟩
  have he : x j*(4*n : ℕ)=Lax263307.ProjectedOracle.raw x j := by
    simp only [Lax263307.ProjectedOracle.raw,Nat.cast_mul,Nat.cast_ofNat]
    ring
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),
    q_frame (r1.seq (r2.seq r3)) hs (by decide) (by decide) (by decide),by simpa only [he] using p3⟩

theorem vector_spec (B M n : ℕ) (x : Fin n → ℚ)
    (hB : 2*M^2+3<B) (hshape : 4*n+5<B) (hscale : 4*n≤M) (hx : ∀ j,Bounded M (x j)) :
    Spec B (fun σ => Context x σ ∧ 3*n<(σ.arrs "lp.word").length) vector
      (fun _ τ => Q x τ ∧ Prefix (encodeVector (Lax263307.ProjectedOracle.raw x)) "lp.word" τ ∧
        τ.vars "lp.position"=3*n) ((36*M.size+76)*n+12) := by
  have hheight (j : Fin n) : Bounded (M^2) (Lax263307.ProjectedOracle.raw x j) := by
    have hh := NativeScaleFraction.bounds M (4*n) (x j) hscale (hx j)
    have he : x j*(4*n : ℕ)=Lax263307.ProjectedOracle.raw x j := by
      simp only [Lax263307.ProjectedOracle.raw,Nat.cast_mul,Nat.cast_ofNat]
      ring
    simpa only [he] using hh
  have hh := RamVectorEncoding.command_spec B (36*M.size+41) (Q x) "scale.i" "vec.n"
    (List.ofFn (Lax263307.ProjectedOracle.raw x)) [] read (by omega) (by simp; omega)
    (by intro i hi; simp only [List.getElem_ofFn]; exact (hheight ⟨i,by simpa using hi⟩).1.trans_lt (by omega))
    (by intro i hi; simp only [List.getElem_ofFn]; exact (hheight ⟨i,by simpa using hi⟩).2.trans_lt (by omega))
    (fun σ hs => by simpa only [List.length_ofFn] using hs.1.1)
    (fun σ k hs => by simpa only [Q,Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using hs)
    (fun i hi => by simpa only [List.getElem_ofFn] using read_spec B M n x i (by simpa using hi) hB hshape hscale hx)
    (by decide) (by decide) (by decide) (by decide)
    (fun rr hs => q_frame rr hs (by decide) (by decide) (by decide)) (by decide)
  rintro σ ⟨hs,hroom⟩
  obtain ⟨ν,r1,p1⟩ := setup_spec B n x hshape σ hs
  obtain ⟨τ,r2,p2⟩ := hh ν ⟨p1.1,by simp [Prefix],by simpa only [List.length_nil] using p1.2,
    by simpa only [List.length_nil,Nat.zero_add,List.length_ofFn,RamFrames.run_array_length r1] using hroom⟩
  exact ⟨τ,(r1.seq r2).mono (by simp only [List.length_ofFn]; nlinarith only []),p2.1,
    by simpa only [List.nil_append,RamVectorEncoding.encode,encodeVector] using p2.2.1,
    by simpa only [List.length_nil,Nat.zero_add,List.length_ofFn] using p2.2.2⟩

/-- Form the projection query's scaled center from the actual stored
rounded center, emitting reduced rationals into its dedicated buffer. -/
theorem command_spec (B M n : ℕ) (x : Fin n → ℚ)
    (hB : 2*M^2+3<B) (hshape : 4*n+5<B) (hscale : 4*n≤M) (hx : ∀ j,Bounded M (x j)) :
    Spec B (fun σ => Context x σ ∧ 3*n<(σ.arrs "lp.word").length ∧
      3*n≤(σ.arrs "projection.center").length) command
      (fun _ τ => Context x τ ∧ Prefix (encodeVector (Lax263307.ProjectedOracle.raw x)) "projection.center" τ)
      ((36*M.size+124)*n+22) := by
  have hlen := NativeRoundedQuery.vector_length (Lax263307.ProjectedOracle.raw x)
  have hw := NativeRationalBounds.vector_words B (M^2) n (Lax263307.ProjectedOracle.raw x) (by omega) (by omega)
    (fun j => by
      have hh := NativeScaleFraction.bounds M (4*n) (x j) hscale (hx j)
      simpa only [Lax263307.ProjectedOracle.raw,Nat.cast_mul,Nat.cast_ofNat,mul_comm] using hh)
  rintro σ ⟨hs,hword,hroom⟩
  obtain ⟨ν,r1,p1⟩ := vector_spec B M n x hB hshape hscale hx σ ⟨hs,hword⟩
  obtain ⟨τ,r2,p2⟩ := NativeProgramCache.copy_spec B "lp.word" "projection.center" "lp.position"
    (encodeVector (Lax263307.ProjectedOracle.raw x)) (by decide) (by rw [hlen]; omega) hw ν
    ⟨p1.2.1,by simpa only [hlen] using p1.2.2,by rw [hlen,RamFrames.run_array_length r1]; exact hroom⟩
  exact ⟨τ,(r1.seq r2).mono (by rw [hlen]; nlinarith only []),
    (q_frame r2 p1.1 (by decide) (by decide) (by decide)).1,p2.2⟩

end Lax263307Proofs.NativeProjectionCenter
