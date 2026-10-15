import Lax263307Proofs.NativeSelectedBudget
import Lax263307Proofs.NativeExhaustiveResources

set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeLocalTime

open Lax263307 AlgorithmParameters NativeCoreMachine NativeSelectedRounds NativePolynomialEnvelope

def rows (W : ℕ) : ℕ := 2+W*(W+4)
def inputLength (W : ℕ) : ℕ := 2+3*(rows W*W)+3*(rows W+W)
def inputCost (W : ℕ) : ℕ := (22*W+129)*(rows W*W)+57*(rows W+W)+111
def catalog (W : ℕ) : ℕ := (54*(W+1)*(W+3)+(69*W+33)*W+41)*(W+3)+8
def moment (W : ℕ) : ℕ := catalog W+(38*W*W+42*W+60)*W+18
def entry (cfg : Config) (W : ℕ) : ℕ := 36*W+12*(4*cfg.a+2)+88
def large (cfg : Config) (W : ℕ) : ℕ := 36*W+12*(4*cfg.a+2)+76+moment W+
  inputCost W+16*inputLength W+12*W+105*(W*W)+91*W+108
def component (W : ℕ) : ℕ := (36*(2*((2*W+1)*(W+1))+1)+258)*W+72
def part (cfg : Config) (W S : ℕ) : ℕ := 43*W+37+component W+
  ((16*S+8)*(frameArrays cfg).length+7*(frameScalars cfg).length+52*(W*W)+36)+
  ((16*S+16)*(frameArrays cfg).length+7*(frameScalars cfg).length+12)+
  ((45*W+38)+((28*W+104)*W+30))
def near (cfg : Config) (W S : ℕ) : ℕ := (48*W+2000*(4*W+20)^6+14)+10+
  ((17*W+72*(2*W+1)+270)*W+17*W+67)+(W+10)+part cfg W S*(W+1)+10
def oracle (cfg : Config) (W S : ℕ) : ℕ :=
  (16*inputLength W+(36*(100*(W+1)+1)+124)*W+135+W+2)+14+(193*W+48)+near cfg W S+6
def steps (W : ℕ) : ℕ := 2+(5*(W+1)+7)*W
def branches (W : ℕ) : ℕ := (W+1)*W
def time (cfg : Config) (W S : ℕ) : ℕ := entry cfg W+large cfg W+2+(oracle cfg W S+W)*W+300*(W+2)^3

theorem row_bound (n r W : ℕ) (hn : n ≤ W) (hN : MomentLP.dimension n r ≤ W) :
    NativeMomentAssembly.rowCount n r ≤ rows W := by
  rw [show NativeMomentAssembly.rowCount n r=2+MomentLP.dimension n r*(n+4) by
    simpa only [NativeMomentInput.M] using NativeMomentInput.row_count_eq n r]
  exact Nat.add_le_add_left (Nat.mul_le_mul hN (Nat.add_le_add_right hn 4)) 2

theorem input_length (n r W : ℕ) (hn : n ≤ W) (hN : MomentLP.dimension n r ≤ W) :
    NativeMomentInput.length n r ≤ inputLength W := by
  have hm := row_bound n r W hn hN
  dsimp only [NativeMomentInput.length,NativeMomentInput.M,inputLength]
  gcongr

theorem entry_bound (cfg : Config) (n W : ℕ) (hn : n ≤ W) : NativeNodeTrace.entryCost cfg.a n ≤ entry cfg W := by
  have hs : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have ht : (2*n).size ≤ 2*n := Nat.size_le.mpr Nat.lt_two_pow_self
  dsimp only [NativeNodeTrace.entryCost,entry]
  omega

theorem large_bound (cfg : Config) (n r W : ℕ) (hn : n ≤ W) (hr : r ≤ W) (hN : MomentLP.dimension n r ≤ W) :
    NativeLargeNode.cost cfg.a n r ≤ large cfg W := by
  have hs : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have ht : (2*n).size ≤ 2*n := Nat.size_le.mpr Nat.lt_two_pow_self
  have hm := row_bound n r W hn hN
  have hi := input_length n r W hn hN
  have hmoment : NativeMomentSetup.cost n r ≤ moment W := by
    dsimp only [NativeMomentSetup.cost,NativeMomentSetup.catalogCost,NativeMomentSetup.N,moment,catalog]
    gcongr
  have hinput : NativeMomentInput.cost n r ≤ inputCost W := by
    dsimp only [NativeMomentInput.cost,NativeMomentInput.M,inputCost]
    gcongr
  dsimp only [NativeLargeNode.cost,NativeLargeSetup.timeBound,large]
  have hNN := Nat.mul_self_le_mul_self hN
  nlinarith only [hs,ht,hn,hr,hN,hmoment,hinput,hi,hNN]

theorem component_bound (n H W : ℕ) (hn : n ≤ W) (hH : H ≤ W) :
    NativeComponentDecision.timeBound n (2*H) ≤ component W := by
  simp only [NativeComponentDecision.timeBound,NativeComponentDecision.height,
    NativeQuadraticResources.square_power,Nat.size_pow,component]
  gcongr

theorem part_bound (cfg : Config) (n r H W S : ℕ) (hn : n ≤ W) (hN : MomentLP.dimension n r ≤ W) (hH : H ≤ W) :
    NativeCollectionExecution.partCost cfg n r S (2*H) 0 ≤ part cfg W S := by
  have hc := component_bound n H W hn hH
  dsimp only [NativeCollectionExecution.partCost,part]
  simp only [Nat.add_zero]
  gcongr

theorem near_bound (cfg : Config) (n r H W S T : ℕ)
    (hn : n ≤ W) (hr : r ≤ W) (hN : MomentLP.dimension n r ≤ W) (hH : H ≤ W) (hT : T ≤ W) :
    NativeNearExecution.timeBound cfg n r (2^H) S (2*H) 0 T ≤ near cfg W S := by
  have hh := NativeHeavyResources.cost_bound n r H
  have hbase : n+r+NativeCatalogMetadata.N n r+H+20 ≤ 4*W+20 := by
    change n+r+MomentLP.dimension n r+H+20 ≤ 4*W+20
    omega
  have hheavy : NativeHeavySearch.cost (2^H) n r ≤ 2000*(4*W+20)^6 :=
    hh.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase 6))
  have hp := part_bound cfg n r H W S hn hN hH
  simp only [NativeNearExecution.timeBound,NativeQuadraticResources.square_power,Nat.size_pow,near]
  gcongr

theorem oracle_bound {lp flow : List ℕ → List ℕ} (cfg : Config) (p : NativeSelectedLP.Program lp)
    (q : NativeSelectedNear.Program flow) (n D k R W S : ℕ)
    (hR : R ≤ W) (hn : n ≤ W) (hr : level cfg n D ≤ W) (hN : N cfg n D ≤ W) (hH : H p R ≤ W)
    (hcall : NativeSelectedLP.callCost p R ≤ W) (hflow : flowTime cfg p q n D k R ≤ W) :
    oracleLocal cfg p q n D k R S ≤ oracle cfg W S := by
  have hi := input_length n (level cfg n D) W hn hN
  have hnear := near_bound cfg n (level cfg n D) (H p R) W S (flowTime cfg p q n D k R) hn hr hN hH hflow
  simp only [oracleLocal,Nat.size_pow,oracle]
  gcongr

theorem polynomial (cfg : Config) : Bounded (fun W => steps W+branches W+time cfg W (2*(W+1))) := by
  simp only [steps,branches,time,entry,large,moment,catalog,inputCost,inputLength,rows,oracle,near,part,component]
  polynomial_envelope

end Lax263307Proofs.NativeLocalTime
