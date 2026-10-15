import Lax263307Proofs.NativeNearExecution
import Lax263307Proofs.NativeHeavyResources

set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeNearResources

open Lax263307 NativeCoreMachine

def buffers : List String := ["child.graph","search.graph","subset.bits","restrict.vertices","lp.word",
  "cut.source","sum.input","near.moments","near.costs","lp.input","round.normal","separator.pieces"]

def space (R : ℕ) : ℕ := 10*(R+1)^2

def wordHeight (cfg : Config) (R H S cursor : ℕ) : ℕ :=
  (36*(5*R+H+20)^4+10)+
  (2*((2*H+1)*(R+1))+4*(3*R+20)+20)+
  (cursor+S*(frameArrays cfg).length+(frameScalars cfg).length+R*R+2*R+
    2*(R+1)+(R+1)+(2*R+2)+3*R+80)+100

/-- All near/conditioning/collection numeric fields are obtained from a
root polynomial height and buffer budget. These bounds do not use host
word height as a bound on rational certificate coordinates. -/
theorem bounds (cfg : Config) (n r D k p fuel S H R w : ℕ) (extent : String → ℕ) (front : List ℕ)
    (hn : 0<n) (hD : 0<D) (hp : 0<p) (hnR : n≤R) (hrR : r≤R) (hDR : D≤R)
    (hkR : k≤R) (hpR : p≤R) (hNR : NativeCatalogMetadata.N n r≤R) (hf : fuel≤2*R+2)
    (hw : wordHeight cfg R H S front.length≤w)
    (hext : ∀ a∈frameArrays cfg,extent a=S)
    (hstack : front.length+S*(frameArrays cfg).length+(frameScalars cfg).length≤extent "recursion.frames")
    (hroom : ∀ a∈buffers,space R≤extent a) :
    NativeNearExecution.Bounds n r D k p (2^H) (2*H) (R+1) fuel S w cfg extent front := by
  have hspan : NativeHeavyResources.span n r k p H≤5*R+H+20 := by
    dsimp only [NativeHeavyResources.span]; omega
  have hheavy : NativeHeavyResources.wordExponent n r k p H≤36*(5*R+H+20)^4+10 := by
    dsimp only [NativeHeavyResources.wordExponent]
    gcongr
  have hwHeavy : NativeHeavyResources.wordExponent n r k p H≤w := by
    dsimp only [wordHeight] at hw
    omega
  have guards := NativeHeavyResources.guards n r k p H w hwHeavy
  have hcomponent : NativeComponentDecision.wordHeight n D k (2*H)≤
      2*((2*H+1)*(R+1))+4*(3*R+20)+20 := by
    dsimp only [NativeComponentDecision.wordHeight,NativeComponentResources.span]
    gcongr <;> omega
  have hwComponent : NativeComponentDecision.wordHeight n D k (2*H)≤w := by
    dsimp only [wordHeight] at hw
    omega
  have hnn : n*n≤R*R := Nat.mul_self_le_mul_self hnR
  have hcollection : front.length+S*(frameArrays cfg).length+(frameScalars cfg).length+n*n+2*n+
      2*(n+1)+(R+1)+fuel+3*NativeCatalogMetadata.N n r+80≤w := by
    dsimp only [wordHeight] at hw
    omega
  have hreply : n+19<2^w := by
    have h : n+19≤w := by omega
    exact h.trans_lt Nat.lt_two_pow_self
  have hspace : n*n+3*n+3*(n*n)+3*NativeCatalogMetadata.N n r+n+1<space R := by
    dsimp only [space]
    nlinarith only [hnn,hnR,hNR,Nat.zero_le (R^2)]
  have room (a : String) (ha : a∈buffers) :
      n*n+3*n+3*(n*n)+3*NativeCatalogMetadata.N n r+n+1<extent a := hspace.trans_le (hroom a ha)
  refine ⟨hn,hD,hp,Nat.one_le_pow _ _ (by decide),hreply,guards.1,guards.2.1,guards.2.2.1,
    guards.2.2.2.1,guards.2.2.2.2.1,guards.2.2.2.2.2.1,guards.2.2.2.2.2.2,?_,hwComponent,
    hcollection.trans_lt Nat.lt_two_pow_self,hext,hstack,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [←pow_mul,Nat.mul_comm H 2]
  · have h := room "child.graph" (by simp [buffers]); omega
  · have h := room "search.graph" (by simp [buffers]); omega
  · have h := room "subset.bits" (by simp [buffers]); omega
  · have h := room "restrict.vertices" (by simp [buffers]); omega
  · have h := room "lp.word" (by simp [buffers]); omega
  · have h := room "cut.source" (by simp [buffers]); omega
  · have h := room "sum.input" (by simp [buffers]); omega
  · have h := room "near.moments" (by simp [buffers]); omega
  · have h := room "near.costs" (by simp [buffers]); omega
  · have h := room "lp.input" (by simp [buffers]); omega
  · have h := room "round.normal" (by simp [buffers]); omega
  · have h := room "separator.pieces" (by simp [buffers]); omega

end Lax263307Proofs.NativeNearResources
