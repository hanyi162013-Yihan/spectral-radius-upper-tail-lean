import SpectralRadiusUpperTail.MatrixWordWalkExpansion
import SpectralRadiusUpperTail.MatrixTraceMoments
import Mathlib.Algebra.BigOperators.Group.List.Basic

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix
variable {ι 𝕂 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕂]

/-- The ordered block word (+^m -^m)^q; no commutation is used. -/
def matrixGramWord (A : Matrix ι ι 𝕂) (m q : ℕ) : List (Matrix ι ι 𝕂) :=
  (List.replicate q (List.replicate m A ++ List.replicate m Aᴴ)).flatten

lemma matrixGramWord_prod (A : Matrix ι ι 𝕂) (m q : ℕ) :
    (matrixGramWord A m q).prod = (A^m * (A^m)ᴴ)^q := by
  simp only [matrixGramWord, List.prod_flatten, List.map_replicate,
    List.prod_replicate, List.prod_append, Matrix.conjTranspose_pow]

lemma matrixGramWord_length (A : Matrix ι ι 𝕂) (m q : ℕ) :
    (matrixGramWord A m q).length = q*(2*m) := by
  simp [matrixGramWord, List.length_flatten, two_mul]

lemma matrixGramWord_trace (A : Matrix ι ι 𝕂) (m q : ℕ) :
    RCLike.re (matrixGramWord A m q).prod.trace = matrixTraceMoment q (A^m) := by
  rw [matrixGramWord_prod]
  rfl

lemma matrixGramWord_trace_walk (A : Matrix ι ι 𝕂) (m q : ℕ) :
    matrixTraceMoment q (A^m) = RCLike.re
      (∑ i, ∑ v : Fin (matrixGramWord A m q).length → ι,
        matrixWordWalkTerm (fun j => (1 : Matrix ι ι 𝕂) j i)
          (matrixGramWord A m q) i v) := by
  rw [← matrixWord_trace_walk_sum, mul_one, matrixGramWord_trace]

#print axioms matrixGramWord
#print axioms matrixGramWord_prod
#print axioms matrixGramWord_length
#print axioms matrixGramWord_trace
#print axioms matrixGramWord_trace_walk
end SpectralRadiusUpperTail
