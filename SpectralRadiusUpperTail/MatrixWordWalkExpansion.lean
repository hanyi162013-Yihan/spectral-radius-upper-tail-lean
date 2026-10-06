import SpectralRadiusUpperTail.MatrixWalkExpansion
import Mathlib.LinearAlgebra.Matrix.Trace

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Semiring R]

/-- A walk through an ordered, possibly noncommuting matrix word. -/
def matrixWordWalkTerm (q : ι → R) :
    (L : List (Matrix ι ι R)) → ι → (Fin L.length → ι) → R
  | [], i, _ => q i
  | A::L, i, v => A i (v 0) * matrixWordWalkTerm q L (v 0) (fun j => v j.succ)

lemma matrixWordWalkTerm_sum (L : List (Matrix ι ι R)) (q : ι → R) (i : ι) :
    (∑ v : Fin L.length → ι, matrixWordWalkTerm q L i v) = L.prod.mulVec q i := by
  induction L generalizing i with
  | nil => simp [matrixWordWalkTerm]
  | cons A L ih =>
    calc
      _ = ∑ z : ι × (Fin L.length → ι),
          matrixWordWalkTerm q (A::L) i ((matrixWalkSplit L.length).symm z) :=
        ((matrixWalkSplit L.length).symm.sum_comp _).symm
      _ = ∑ j, ∑ v : Fin L.length → ι,
          A i j * matrixWordWalkTerm q L j v := by
        rw [Fintype.sum_prod_type]
        rfl
      _ = ∑ j, A i j * L.prod.mulVec q j := by
        simp only [← Finset.mul_sum, ih]
      _ = _ := by
        rw [List.prod_cons, ← Matrix.mulVec_mulVec]
        rfl

lemma matrixWord_trace_walk_sum (L : List (Matrix ι ι R)) (B : Matrix ι ι R) :
    (L.prod * B).trace =
      ∑ i, ∑ v : Fin L.length → ι, matrixWordWalkTerm (fun j => B j i) L i v := by
  simp_rw [matrixWordWalkTerm_sum]
  rfl

#print axioms matrixWordWalkTerm
#print axioms matrixWordWalkTerm_sum
#print axioms matrixWord_trace_walk_sum
end SpectralRadiusUpperTail
