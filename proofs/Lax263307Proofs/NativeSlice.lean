import Lax263307Proofs.NativeTabulate

namespace Lax263307Proofs.NativeSlice

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs

def read (source : String) : Com := .assign "fill.value"
  (.get source (.add (.var "slice.start") (.var "fill.i")))

def command (source target : String) : Com := NativeTabulate.command target (read source)

def Context (source : String) (front xs tail : List ℕ) (σ : Env) : Prop :=
  Prefix (front++(xs++tail)) source σ ∧ σ.vars "slice.start"=front.length

theorem read_spec (B : ℕ) (source : String) (front xs tail : List ℕ)
    (i : ℕ) (hi : i<xs.length) (hB : front.length+xs.length+1<B) (hv : xs[i]<B) :
    Spec B (fun σ => Context source front xs tail σ ∧ σ.vars "fill.i"=i) (read source)
      (fun _ τ => Context source front xs tail τ ∧ τ.vars "fill.value"=xs[i]) 5 := by
  rintro σ ⟨⟨hp,hstart⟩,hindex⟩
  have hlen : front.length+i<(front++(xs++tail)).length := by simp; omega
  have hget : (σ.arrs source)[front.length+i]?=some xs[i] := by
    have hh := hp (front.length+i) hlen
    simpa only [List.getElem_append_right (by omega : front.length≤front.length+i),
      Nat.add_sub_cancel_left,List.getElem_append_left hi] using hh
  have hroom : front.length+i<(σ.arrs source).length := by
    by_contra hh
    rw [List.getElem?_eq_none (by omega)] at hget
    cases hget
  run_vcg
  all_goals simp_all [Context,Prefix]

/-- Copy an initialized slice to another reserved buffer by an actual RAM
loop. No word outside the requested slice is inspected or copied. -/
theorem command_spec (B : ℕ) (source target : String) (front xs tail : List ℕ)
    (hne : source≠target) (hB : front.length+xs.length+1<B) (hv : ∀ z∈xs,z<B) :
    Spec B (fun σ => Context source front xs tail σ ∧ σ.vars "fill.length"=xs.length ∧
      xs.length≤(σ.arrs target).length) (command source target)
      (fun _ τ => Context source front xs tail τ ∧ Prefix xs target τ) (16*xs.length+6) := by
  have hh := NativeTabulate.command_spec B xs target (Context source front xs tail) (read source) 5
    (by omega) hv (by simp [read,Com.wvars]) (by simp [read,Com.wvars])
    (by simp [read,Com.warrs])
    (fun σ h => by simpa only [Context,Prefix,arrs_setVar,vars_setVar,String.reduceEq,if_false] using h)
    (fun σ τ rr h => by
      simpa only [Context,Prefix,rr.frame_arr source (by simp [NativeTabulate.append,RamWordBuffer.append,Com.warrs,hne]),
        rr.frame_var "slice.start" (by simp [NativeTabulate.append,RamWordBuffer.append,Com.wvars])] using h)
    (fun i hi => read_spec B source front xs tail i hi hB (hv _ (List.getElem_mem hi)))
  exact hh

end Lax263307Proofs.NativeSlice
