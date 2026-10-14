import Lax263307Proofs.NativeRationalRead
import Lax263307Proofs.NativeRationalBounds

namespace Lax263307Proofs.NativeCutRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.RationalEncoding NativeSignedArithmetic

def Context {n : ℕ} (a : Fin n → ℚ) (σ : Env) : Prop :=
  Prefix (encodeVector a) "cut.source" σ ∧ σ.vars "projection.n"=n

def command : Com := .seq (.assign "read.cursor" (.mul (.lit 3) (.var "cut.i")))
  (NativeRationalRead.command "cut.source")

theorem command_spec (B M n : ℕ) (a : Fin n → ℚ) (i : Fin n)
    (hM : M<B) (hs : 3*n+10<B) (ha : ∀ j,Bounded M (a j)) :
    Spec B (fun σ => Context a σ ∧ σ.vars "cut.i"=i.val) command
      (fun _ τ => Context a τ ∧ RamRational.FractionOutput (a i) τ) 21 := by
  rintro σ ⟨hc,hi⟩
  let ν := σ.setVar "read.cursor" (3*i.val)
  have r1 : Run B (.assign "read.cursor" (.mul (.lit 3) (.var "cut.i"))) σ ν 4 :=
    Run.assign (evalB_bin (op := .mul) (evalB_lit (by omega : 3<B))
      (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ (by omega : i.val<B)⟩)
      (by change 3*i.val<B; omega))
  obtain ⟨τ,r2,p2⟩ := NativeRationalRead.vector_entry_spec B "cut.source" [] [] (List.ofFn a)
    i.val (by simpa using i.isLt) (by omega) (by simp; omega)
    (by simpa only [List.getElem_ofFn] using (ha i).1.trans_lt hM)
    (by simpa only [List.getElem_ofFn] using (ha i).2.trans_lt hM) ν
    ⟨by simpa only [List.nil_append,List.append_nil,NativeRationalTabulate.words,encodeVector,Prefix,ν,arrs_setVar] using hc.1,
      by simp [ν]⟩
  have rr := r1.seq r2
  refine ⟨τ,rr,?_,by simpa only [List.getElem_ofFn] using p2.1⟩
  simpa only [Context,Prefix,rr.frame_arr "cut.source" (by decide),
    rr.frame_var "projection.n" (by decide)] using hc

end Lax263307Proofs.NativeCutRead
