import Lax263307Proofs.NativeDistanceQueryResources
import Lax263307Proofs.NativeMomentEncodingHeight
import Lax263307Proofs.NativeProjectionCenter
import Lax263307.NativeRoundedStep

namespace Lax263307Proofs.NativeProjectionQueryBounds

open Lax263307 MomentLP
open NativeSignedArithmetic Lax109476.RationalEncoding

abbrev rows (n r : ℕ) : ℕ := 2+(dimension n r+(dimension n r+(dimension n r*n+(dimension n r+dimension n r))))

def scaleHeight (N R : ℕ) : ℕ := 80*(R+1)+4*N+1
def height (n k r R : ℕ) : ℕ := NativeMomentEncodingHeight.height n k r+2*scaleHeight (dimension n r) R+1

def rootHeight (R : ℕ) : ℕ := 100*(4*R+2)^3+10+2*scaleHeight R R+1
def rootRows (R : ℕ) : ℕ := 6*(R+1)^2
def queryBound (R : ℕ) : ℕ := NativeDistanceQueryResources.sizeBound (rootRows R) R (rootHeight R)

/-- The real moment program and the real scaled stored center meet the
LP query's height interface. The polynomial height depends on the root
resource and not on the current numerical VM width. -/
theorem bounded {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r R : ℕ)
    (center : Index n r → ℚ) (hc : ∀ i,NativeRoundedStep.height (center i) (80*(R+1))) :
    NativeDistanceData.Bounded (2^height n k r R) (program G k r) (ProjectedOracle.raw center) := by
  let N := dimension n r
  let s := scaleHeight N R
  let H := height n k r R
  have hH : 0<H := by dsimp [H,height]; omega
  have hsrc : 2^NativeMomentEncodingHeight.height n k r≤2^H :=
    Nat.pow_le_pow_right (by decide) (by dsimp [H,height]; omega)
  have hf := NativeDistanceQueryResources.source_fields _ (program G k r)
    (NativeMomentEncodingHeight.program_words G k r)
  have hpow : 2^(s*2)<2^H := Nat.pow_lt_pow_right (by decide) (by dsimp [H,height,s,N]; omega)
  refine ⟨Nat.one_lt_pow (by omega) (by decide),?_,?_,?_⟩
  · intro i j
    exact ⟨(hf.1 i j).1.trans_le hsrc,(hf.1 i j).2.trans_le hsrc⟩
  · intro i
    exact ⟨(hf.2.1 i).1.trans_le hsrc,(hf.2.1 i).2.trans_le hsrc⟩
  · intro i
    have hscale : 4*N≤2^s := (show 4*N≤s by dsimp [s,scaleHeight]; omega).trans Nat.lt_two_pow_self.le
    have hs : 2^(80*(R+1))≤2^s := Nat.pow_le_pow_right (by decide) (by dsimp [s,scaleHeight]; omega)
    have hi : Bounded (2^s) (center i) := ⟨(hc i).1.trans hs,(hc i).2.trans hs⟩
    have hr : Bounded ((2^s)^2) (ProjectedOracle.raw center i) := by
      have hh := NativeScaleFraction.bounds (2^s) (4*N) (center i) hscale hi
      simpa only [ProjectedOracle.raw,Nat.cast_mul,Nat.cast_ofNat,mul_comm] using hh
    have hpow' : (2^s)^2<2^H := by simpa only [pow_mul] using hpow
    exact ⟨hr.1.trans_lt hpow',hr.2.trans_lt hpow'⟩

/-- One polynomial query envelope covers all nodes and all local iterates. -/
theorem uniform_query_size {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r R : ℕ)
    (hn : n≤R) (hk : k≤R) (hr : r≤R) (hN : dimension n r≤R)
    (center : Index n r → ℚ) (hc : ∀ i,NativeRoundedStep.height (center i) (80*(R+1))) :
    Lax759944.BinaryWordEncoding.bitSize
      (encodeProgram (DistanceProjection.distanceProgram (program G k r) (ProjectedOracle.raw center)))≤queryBound R := by
  have hsize := NativeDistanceQueryResources.query_size (height n k r R) (program G k r)
    (ProjectedOracle.raw center) (bounded G k r R center hc)
  have hm : rows n r≤rootRows R := by
    have hprod := Nat.mul_le_mul hN hn
    dsimp [rows,rootRows]
    nlinarith only [hprod,hN]
  have hsrc : NativeMomentEncodingHeight.height n k r≤100*(4*R+2)^3+10 := by
    apply Nat.add_le_add_right
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    change n+k+r+dimension n r+2≤4*R+2
    omega
  have hH : height n k r R≤rootHeight R := by
    dsimp [height,rootHeight,scaleHeight]
    omega
  apply hsize.trans
  dsimp [queryBound,NativeDistanceQueryResources.sizeBound]
  apply Nat.mul_le_mul
  · dsimp [NativeDistanceData.wordLength,NativeDistanceData.rows,NativeDistanceData.columns]
    gcongr
  · change height n k r R+rows n r+2*dimension n r+4≤rootHeight R+rootRows R+2*R+4
    omega

/-- The explicit root query envelope is an ordinary degree-six polynomial. -/
theorem polynomial_bound (R : ℕ) : queryBound R≤1000000*(R+1)^6 := by
  let S := R+1
  have hS : 1≤S := by dsimp [S]; omega
  have hR : R≤S := by dsimp [S]; omega
  have h12 : S≤S^2 := le_self_pow hS (by omega)
  have h13 : S≤S^3 := le_self_pow hS (by omega)
  have h23 : S^2≤S^3 := Nat.pow_le_pow_right hS (by omega)
  have h03 : 1≤S^3 := Nat.one_le_pow _ _ hS
  have hc : 100*(4*R+2)^3≤6400*S^3 := by
    calc
      _≤100*(4*S)^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [S]; omega) _)
      _=_ := by ring
  have hheight : rootHeight R≤7000*S^3 := by
    dsimp [rootHeight,scaleHeight]
    change 100*(4*R+2)^3+10+2*(80*S+4*R+1)+1≤7000*S^3
    nlinarith only [hc,hR,h13,h03]
  have hrows : rootRows R+2*R≤8*S^2 := by
    change 6*S^2+2*R≤8*S^2
    nlinarith only [hR,h12]
  have hprod : (rootRows R+2*R)*S≤8*S^3 := by
    simpa only [pow_succ,Nat.mul_assoc] using Nat.mul_le_mul_right S hrows
  have hwords : NativeDistanceData.wordLength (rootRows R) R≤60*S^3 := by
    have hexpr : 2+3*((rootRows R+2*R)*S+(rootRows R+2*R)+S)≤60*S^3 := by
      nlinarith only [hprod,hrows,h23,h13,h03]
    simpa only [NativeDistanceData.wordLength,NativeDistanceData.rows,NativeDistanceData.columns,S,Nat.two_mul] using hexpr
  have hfactor : rootHeight R+rootRows R+2*R+4≤8000*S^3 := by
    nlinarith only [hheight,hrows,h23,h03]
  calc
    queryBound R≤(60*S^3)*(8000*S^3) := Nat.mul_le_mul hwords hfactor
    _=480000*S^6 := by ring
    _≤1000000*S^6 := Nat.mul_le_mul_right _ (by decide)

end Lax263307Proofs.NativeProjectionQueryBounds
