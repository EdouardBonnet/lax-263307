import Lax263307Proofs.NativeMomentRows
import Lax263307Proofs.NativeRationalTabulate

namespace Lax263307Proofs.NativeMomentAssembly

open Lax263307 Lax109476.RationalEncoding
open MomentLP CoordinateCatalog

/-- Each block is emitted in its native finite index order. -/
def matrixWords {m n : ℕ} (A : Fin m → Fin n → ℚ) : List ℕ :=
  (List.ofFn fun i => List.ofFn (A i)).flatten.flatMap encodeRational

theorem ofFn_addCases {α : Type*} {m n : ℕ} (f : Fin m → α) (g : Fin n → α) :
    List.ofFn (Fin.addCases f g)=List.ofFn f++List.ofFn g := by
  simpa only [Fin.append] using List.ofFn_fin_append f g

theorem matrix_addCases {a b n : ℕ} (f : Fin a → Fin n → ℚ) (g : Fin b → Fin n → ℚ) :
    matrixWords (Fin.addCases f g)=matrixWords f++matrixWords g := by
  have he : (fun i => List.ofFn (Fin.addCases f g i))=
      Fin.addCases (fun i => List.ofFn (f i)) (fun i => List.ofFn (g i)) := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp
    · intro j; simp
  simp only [matrixWords,he,ofFn_addCases,List.flatten_append,List.flatMap_append]

def normalization (n r : ℕ) : Fin 2 → Index n r → ℚ :=
  fun i j => if i=0 then singleRow ∅ j else -singleRow ∅ j

def upper (n r : ℕ) : Index n r → Index n r → ℚ := fun i => singleRow (indexing n r i).val

def nonindependent {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : ℕ) : Index n r → Index n r → ℚ :=
  fun i j => if G.IsIndepSet ((indexing n r i).val : Set (Fin n)) then 0 else singleRow (indexing n r i).val j

def monotone (n r : ℕ) : Fin (dimension n r*n) → Index n r → ℚ :=
  fun i => let uv := finProdFinEquiv.symm i
    if (indexing n r uv.1).val.card≤r+1 then monotoneRow (indexing n r uv.1).val uv.2 else fun _ => 0

def massPositive (n k r : ℕ) : Index n r → Index n r → ℚ :=
  fun i => if (indexing n r i).val.card≤r+1 then massRow (indexing n r i).val k else fun _ => 0

def massNegative (n k r : ℕ) : Index n r → Index n r → ℚ :=
  fun i j => if (indexing n r i).val.card≤r+1 then -massRow (indexing n r i).val k j else 0

theorem matrix_words_exact {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ) :
    matrixWords (MomentLP.program G k r).A=
      matrixWords (normalization n r)++(matrixWords (upper n r)++
        (matrixWords (nonindependent G r)++(matrixWords (monotone n r)++
          (matrixWords (massPositive n k r)++matrixWords (massNegative n k r))))) := by
  change matrixWords (Fin.addCases (normalization n r) (Fin.addCases (upper n r)
    (Fin.addCases (nonindependent G r) (Fin.addCases (monotone n r)
      (Fin.addCases (massPositive n k r) (massNegative n k r))))))=_
  simp only [matrix_addCases]

theorem matrix_length {m n : ℕ} (A : Fin m → Fin n → ℚ) : (matrixWords A).length=3*m*n := by
  change (NativeRationalTabulate.words ((List.ofFn fun i => List.ofFn (A i)).flatten)).length=3*m*n
  rw [NativeRationalTabulate.words_length]
  simp [List.length_flatten,List.map_ofFn,List.sum_ofFn,Nat.mul_assoc]

def rowCount (n r : ℕ) : ℕ :=
  2+(dimension n r+(dimension n r+(dimension n r*n+(dimension n r+dimension n r))))

def boundWords (n r : ℕ) : List ℕ :=
  [0,1,1,1,1,1]++(List.replicate (dimension n r) [0,1,1]).flatten++
    (List.replicate (dimension n r+(dimension n r*n+(dimension n r+dimension n r))) [0,0,1]).flatten

def objectiveWords (n r : ℕ) : List ℕ := (List.replicate (dimension n r) [0,0,1]).flatten

theorem bound_words_exact {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ) :
    encodeVector (MomentLP.program G k r).b=boundWords n r := by
  simp only [encodeVector,MomentLP.program,ofFn_addCases,List.flatMap_append]
  simp [boundWords,encodeRational,List.ofFn_succ,List.flatMap_replicate,List.ofFn_const]

theorem objective_words_exact {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ) :
    encodeVector (MomentLP.program G k r).c=objectiveWords n r := by
  simp [encodeVector,MomentLP.program,objectiveWords,encodeRational,List.flatMap_replicate,List.ofFn_const]

theorem input_words_exact {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ) :
    encodeProgram (MomentLP.program G k r)=
      [rowCount n r,dimension n r]++
        (matrixWords (normalization n r)++(matrixWords (upper n r)++
          (matrixWords (nonindependent G r)++(matrixWords (monotone n r)++
            (matrixWords (massPositive n k r)++matrixWords (massNegative n k r))))))++
        boundWords n r++objectiveWords n r := by
  change [rowCount n r,dimension n r]++matrixWords (MomentLP.program G k r).A++
    encodeVector (MomentLP.program G k r).b++encodeVector (MomentLP.program G k r).c=_
  rw [matrix_words_exact,bound_words_exact,objective_words_exact]

end Lax263307Proofs.NativeMomentAssembly
