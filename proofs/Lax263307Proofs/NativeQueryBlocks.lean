import Lax263307Proofs.NativeAppendBuffer

namespace Lax263307Proofs.NativeQueryBlocks

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

def command (source : String) (count : Expr) : Com := .seq (.assign "query.length" count)
  (NativeAppendBuffer.command source "lp.word" "query.i" "lp.position" "query.length")

/-- Append an actual initialized data block to the current query. The
copy length is evaluated from source metadata, not supplied as advice. -/
theorem command_spec (B : ℕ) (source : String) (count : Expr) (front xs : List ℕ)
    (hne : source≠"lp.word") (hB : front.length+xs.length+2<B) (hv : ∀ z∈xs,z<B) :
    Spec B (fun σ => Prefix xs source σ ∧ Prefix front "lp.word" σ ∧
      σ.vars "lp.position"=front.length ∧ count.evalB B σ=some xs.length ∧
      front.length+xs.length≤(σ.arrs "lp.word").length) (command source count)
      (fun _ τ => Prefix xs source τ ∧ Prefix (front++xs) "lp.word" τ ∧
        τ.vars "lp.position"=front.length+xs.length) (16*xs.length+count.size+7) := by
  rintro σ ⟨hs,hf,hpos,hcount,hroom⟩
  let ν := σ.setVar "query.length" xs.length
  have r1 : Run B (.assign "query.length" count) σ ν (count.size+1) :=
    (Run.assign hcount).mono (by omega)
  obtain ⟨τ,r2,p2⟩ := NativeAppendBuffer.command_spec B source "lp.word" "query.i" "lp.position" "query.length"
    front xs (by dsimp [NativeAppendBuffer.Names]; decide) hne hB hv ν
    ⟨hs,hf,by simpa only [ν,vars_setVar,String.reduceEq,if_false] using hpos,by simp [ν],hroom⟩
  exact ⟨τ,(r1.seq r2).mono (by omega),p2⟩

end Lax263307Proofs.NativeQueryBlocks
