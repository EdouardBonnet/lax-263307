import Lax263307Proofs.NativeComponentNormal
import Lax263307Proofs.NativeClearNormal

namespace Lax263307Proofs.NativeOracleCut

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 NativeSignedArithmetic

def far (next : ℕ) : Com := .seq NativeClearNormal.command
  (.seq (NativeProgramCache.copy "lp.word" "round.normal" "lp.position") (.assign "machine.phase" (.lit next)))

/-- The far-projection phase clears denominators, stores the actual normal,
and transfers control to the rounded-update phase. -/
theorem far_spec (B M n next : ℕ) (a : Fin n → ℚ)
    (hB : M*RationalCutBuffer.denominator a+M+RationalCutBuffer.denominator a+3*n+next+10<B)
    (ha : ∀ j,Bounded M (a j)) :
    Spec B (fun σ => NativeArrayBounds.Bounded B σ ∧ Prefix (encodeVector a) "lp.word" σ ∧
      σ.vars "projection.n"=n ∧ 3*n≤(σ.arrs "cut.source").length ∧
      3*n<(σ.arrs "lp.word").length ∧ 3*n≤(σ.arrs "round.normal").length)
      (far next) (fun _ τ => Prefix (NativeRoundedQuery.normal (RationalCutBuffer.integerNormal a)) "round.normal" τ ∧
        τ.vars "machine.phase"=next) (193*n+40) := by
  rintro σ ⟨hb,hp,hn,hc,ho,hr⟩
  obtain ⟨ν,r1,p1⟩ := NativeClearNormal.command_spec B M n a (by omega) ha σ ⟨hp,hn,hc,ho⟩
  have hlen : (encodeVector (fun i => (RationalCutBuffer.integerNormal a i : ℚ))).length=3*n :=
    NativeRoundedQuery.vector_length _
  obtain ⟨μ,r2,p2⟩ := NativeProgramCache.copy_spec B "lp.word" "round.normal" "lp.position" _ (by decide)
    (by rw [hlen]; omega) (NativeArrayBounds.prefix_words (NativeArrayBounds.run r1 hb) p1.1) ν
    ⟨p1.1,by simpa only [hlen] using p1.2.1,by rw [hlen,RamFrames.run_array_length r1]; exact hr⟩
  let τ := μ.setVar "machine.phase" next
  have r3 : Run B (.assign "machine.phase" (.lit next)) μ τ 2 := Run.assign (evalB_lit (show next<B by omega))
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by rw [hlen]; omega),p2.2,by simp [τ]⟩

def failedChild (next : ℕ) : Com := .seq
  (.assign "component.target" (.sub (.var "component.target") (.lit 1)))
  (.seq NativeComponentNormal.command (.assign "machine.phase" (.lit next)))

/-- A failed child target t produces the cut with bound t-1, exactly as
ComputedRounding.collect specifies, then enters the rounded-update phase. -/
theorem failed_child_spec {n : ℕ} (B r next : ℕ) (A C : Finset (Fin n)) (t : ℕ)
    (hB : n+t+3*NativeCatalogMetadata.N n r+next+10<B) (hm : 2^n<B) :
    Spec B (fun σ => NativeComponentNormal.Data r A C t σ ∧ NativeArrayBounds.Bounded B σ ∧
      3*NativeCatalogMetadata.N n r≤(σ.arrs "lp.input").length ∧
      3*NativeCatalogMetadata.N n r≤(σ.arrs "round.normal").length)
      (failedChild next) (fun _ τ => Prefix (NativeRoundedQuery.normal
        (RationalCutBuffer.integerNormal (RoundedOracleSearch.rationalNormal
          (NativeComponentNormal.normal (r:=r) A C (t-1))))) "round.normal" τ ∧ τ.vars "machine.phase"=next)
      ((28*n+104)*NativeCatalogMetadata.N n r+26) := by
  rintro σ ⟨hd,hb,hlp,hr⟩
  let ν := σ.setVar "component.target" (t-1)
  have r1 : Run B (.assign "component.target" (.sub (.var "component.target") (.lit 1))) σ ν 4 :=
    Run.assign (evalB_bin (op:=.sub)
      (by rw [evalB_var_iff]; exact ⟨hd.target.symm,hd.target ▸ (by omega)⟩)
      (evalB_lit (show 1<B by omega)) (by change t-1<B; omega))
  have d1 : NativeComponentNormal.Data r A C (t-1) ν :=
    ⟨(r1.frame_var _ (by decide)).trans hd.order,(r1.frame_var _ (by decide)).trans hd.count,
      hd.catalog,(r1.frame_var _ (by decide)).trans hd.conditioning,
      (r1.frame_var _ (by decide)).trans hd.component,by simp [ν]⟩
  obtain ⟨μ,r2,p2⟩ := NativeComponentNormal.command_spec B r A C (t-1) (by omega) hm ν
    ⟨d1,NativeArrayBounds.run r1 hb,by rwa [RamFrames.run_array_length r1],
      by rwa [RamFrames.run_array_length r1]⟩
  let τ := μ.setVar "machine.phase" next
  have r3 : Run B (.assign "machine.phase" (.lit next)) μ τ 2 := Run.assign (evalB_lit (show next<B by omega))
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),p2.2,by simp [τ]⟩

end Lax263307Proofs.NativeOracleCut
