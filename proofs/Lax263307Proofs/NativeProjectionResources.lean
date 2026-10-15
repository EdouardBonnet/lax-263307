import Lax263307Proofs.NativeOracleExecution
import Lax263307Proofs.NativeProjectionQueryBounds

set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeProjectionResources

open Lax263307 Lax109476.RationalEncoding

def buffers : List String := ["lp.input","lp.word","projection.center","projection.tolerance",
  "vm.addresses","vm.values","vm.output","cut.source","round.normal"]

def shape (R : ℕ) : ℕ :=
  NativeDistanceData.shapeSize (NativeProjectionQueryBounds.rootRows R) R+1000*(R+1)^5+20

def space (R T : ℕ) : ℕ := shape R+T+10

def wordHeight (R : ℕ) : ℕ := 200*(R+1)+shape R

theorem tolerance_guard (n D F R : ℕ) (hn : n≤R) (hD : D≤R) (hF : F≤R) :
    NativeNodeTolerance.guard n D F≤1000*(R+1)^5 := by
  have hs : NativeNodeTolerance.guard n D F≤NativeNodeTolerance.guard R R R := by
    dsimp only [NativeNodeTolerance.guard,NativeNodeTolerance.denominator]
    gcongr
  apply hs.trans
  dsimp only [NativeNodeTolerance.guard,NativeNodeTolerance.denominator]
  nlinarith only [Nat.zero_le (R^5),Nat.zero_le (R^4),Nat.zero_le (R^3),Nat.zero_le (R^2),Nat.zero_le R]

theorem rows_bound (n r R : ℕ) (hn : n≤R) (hN : MomentLP.dimension n r≤R) :
    NativeMomentAssembly.rowCount n r≤NativeProjectionQueryBounds.rootRows R := by
  have hprod := Nat.mul_le_mul hN hn
  dsimp only [NativeMomentAssembly.rowCount,NativeProjectionQueryBounds.rootRows]
  nlinarith only [hprod,hN]

/-- Every projection preparation and allocation guard has a fixed root
bound; the center height comes from the checked search trajectory. -/
theorem bounds {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D k r F R w T : ℕ) (extent : String → ℕ)
    (hn : 0<n) (hD : 0<D) (hF : 0<F) (hnR : n≤R) (hDR : D≤R) (hFR : F≤R)
    (hN : MomentLP.dimension n r≤R) (hw : wordHeight R≤w)
    (room : ∀ s∈buffers,space R T≤extent s) :
    NativeOracleExecution.ProjectionBounds D k r F (2^(100*(R+1))) w T G extent := by
  let N := MomentLP.dimension n r
  let m := NativeMomentAssembly.rowCount n r
  have hm : m≤NativeProjectionQueryBounds.rootRows R := by
    have hprod := Nat.mul_le_mul hN hnR
    dsimp only [m,NativeMomentAssembly.rowCount,NativeProjectionQueryBounds.rootRows]
    change 2+(N+(N+(N*n+(N+N))))≤6*(R+1)^2
    change N*n≤R*R at hprod
    nlinarith only [hprod,hN]
  have hshape : NativeDistanceData.shapeSize m N≤
      NativeDistanceData.shapeSize (NativeProjectionQueryBounds.rootRows R) R := by
    dsimp only [NativeDistanceData.shapeSize,NativeDistanceData.wordLength,
      NativeDistanceData.rows,NativeDistanceData.columns]
    gcongr
  have hlen : (encodeProgram (MomentLP.program G k r)).length=
      2+3*(m*N)+3*(m+N) := NativeMomentInput.input_length G k r
  have hmain : (encodeProgram (MomentLP.program G k r)).length+
      NativeDistanceData.wordLength m N+4*N+10≤shape R := by
    have hpow : R+1≤(R+1)^5 := le_self_pow (by omega) (by decide)
    have hpad : 2*N≤1000*(R+1)^5 := by change MomentLP.dimension n r≤R at hN; omega
    calc
      _≤NativeDistanceData.shapeSize m N+2*N := by
        rw [hlen]; dsimp only [NativeDistanceData.shapeSize]; omega
      _≤NativeDistanceData.shapeSize (NativeProjectionQueryBounds.rootRows R) R+1000*(R+1)^5 :=
        Nat.add_le_add hshape hpad
      _≤shape R := by dsimp only [shape]; omega
  have ht := tolerance_guard n D F R hnR hDR hFR
  have hbase : 200*(R+1)+shape R≤w := hw
  have hword : w<2^w := Nat.lt_two_pow_self
  have hsmall : 4*R+20≤w := by
    have hshape0 := Nat.zero_le (shape R)
    omega
  have hrat : 2*(2^(100*(R+1)))^2+3<2^w := by
    have hexp : 2*(100*(R+1))+4≤w := by
      have hh : 4≤shape R := by dsimp only [shape]; omega
      omega
    have hp := Nat.pow_le_pow_right (by decide : 1≤2) hexp
    have he : 2^(2*(100*(R+1))+4)=16*(2^(100*(R+1)))^2 := by
      rw [pow_add,Nat.mul_comm 2 (100*(R+1)),pow_mul]; norm_num; ring
    rw [he] at hp
    have hpos := Nat.one_le_pow (100*(R+1)) 2 (by decide)
    nlinarith only [hp,hpos]
  have scale : 4*N≤2^(100*(R+1)) :=
    (show 4*N≤100*(R+1) by omega).trans Nat.lt_two_pow_self.le
  have inroom (s : String) (hs : s∈buffers) : shape R+T+10≤extent s := room s hs
  refine ⟨hn,hD,hF,?_,hrat,?_,scale,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (by omega : (encodeProgram (MomentLP.program G k r)).length+2≤w).trans_lt hword
  · exact (by omega : 4*MomentLP.dimension n r+5≤w).trans_lt hword
  · have hs : 1000*(R+1)^5≤shape R := by dsimp only [shape]; omega
    exact (ht.trans (by omega)).trans_lt hword
  · exact (by omega : n+19≤w).trans_lt hword
  · have h := inroom "lp.input" (by simp [buffers]); omega
  · have h := inroom "lp.word" (by simp [buffers]); omega
  · have h := inroom "projection.center" (by simp [buffers]); omega
  · have h := inroom "lp.word" (by simp [buffers]); omega
  · have h := inroom "projection.tolerance" (by simp [buffers]); omega
  · have h := inroom "lp.word" (by simp [buffers]); change NativeDistanceData.wordLength m N<extent "lp.word"; omega
  · have h := inroom "vm.addresses" (by simp [buffers]); omega
  · have h := inroom "vm.values" (by simp [buffers]); omega
  · have h := inroom "vm.output" (by simp [buffers]); omega
  · have h := inroom "cut.source" (by simp [buffers]); omega
  · have h := inroom "round.normal" (by simp [buffers]); omega

end Lax263307Proofs.NativeProjectionResources
