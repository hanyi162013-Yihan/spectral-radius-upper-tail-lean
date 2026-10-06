import SpectralRadiusUpperTail.MatrixGramWord
import SpectralRadiusUpperTail.IidSignedWordMoment

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix
variable {ι 𝕂 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕂]

/-- True denotes a conjugate-transposed factor. -/
def signedMatrixFactor (A : Matrix ι ι 𝕂) (s : Bool) : Matrix ι ι 𝕂 :=
  if s then Aᴴ else A

def gramSignWord (m q : ℕ) : List Bool :=
  (List.replicate q (List.replicate m false ++ List.replicate m true)).flatten

lemma matrixGramWord_eq_signed (A : Matrix ι ι 𝕂) (m q : ℕ) :
    (gramSignWord m q).map (signedMatrixFactor A) = matrixGramWord A m q := by
  simp [gramSignWord, matrixGramWord, List.map_flatten, signedMatrixFactor]

lemma signedMatrixFactor_entry (x : ι × ι → 𝕂) (s : Bool) (i j : ι) :
    signedMatrixFactor (Matrix.of (fun i j => x (i,j))) s i j =
      if s then star (x (j,i)) else x (i,j) := by
  cases s <;> rfl

/-- Encode a transposed factor by reversing its underlying iid entry index. -/
lemma signedMatrixFactor_oriented_entry (x : ι × ι → 𝕂) (s : Bool) (i j : ι) :
    signedMatrixFactor (Matrix.of (fun i j => x (i,j))) s i j =
      if s then star (x (if s then (j,i) else (i,j)))
      else x (if s then (j,i) else (i,j)) := by
  cases s <;> rfl

#print axioms signedMatrixFactor
#print axioms gramSignWord
#print axioms matrixGramWord_eq_signed
#print axioms signedMatrixFactor_entry
#print axioms signedMatrixFactor_oriented_entry
end SpectralRadiusUpperTail
