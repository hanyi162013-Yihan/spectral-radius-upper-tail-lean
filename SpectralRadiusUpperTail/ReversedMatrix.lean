import SpectralRadiusUpperTail.ReversedRow
import SpectralRadiusUpperTail.ConcreteTriangular

namespace SpectralRadiusUpperTail
open Matrix
open scoped BigOperators Matrix.Norms.Frobenius
variable {𝕂 : Type*} [RCLike 𝕂] {N : ℕ}

def reverseMatrix (A : Matrix (Fin N) (Fin N) 𝕂) : Matrix (Fin N) (Fin N) 𝕂 :=
  fun i j => A i.rev j.rev

lemma reverseMatrix_sub (A B : Matrix (Fin N) (Fin N) 𝕂) :
    reverseMatrix (A-B) = reverseMatrix A-reverseMatrix B := rfl

lemma reverseMatrix_one : reverseMatrix (1 : Matrix (Fin N) (Fin N) 𝕂) = 1 := by
  ext i j
  simp only [reverseMatrix, Matrix.one_apply, Fin.rev_inj]

lemma reverseMatrix_norm_sq (A : Matrix (Fin N) (Fin N) 𝕂) :
    ‖reverseMatrix A‖^2 = ‖A‖^2 := by
  simp only [frobenius_norm_sq_eq_sum, reverseMatrix]
  calc
    _ = ∑ i : Fin N, ∑ j : Fin N, ‖A i.rev j‖^2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact sum_fin_reverse (fun j : Fin N => ‖A i.rev j‖^2)
    _ = _ := sum_fin_reverse (fun i : Fin N => ∑ j : Fin N, ‖A i j‖^2)

lemma vecMul_reverseMatrix (x : Fin N → 𝕂) (A : Matrix (Fin N) (Fin N) 𝕂) (j : Fin N) :
    (x ᵥ* reverseMatrix A) j = ((fun i : Fin N => x i.rev) ᵥ* A) j.rev := by
  change (∑ i : Fin N, x i*A i.rev j.rev) = ∑ i : Fin N, x i.rev*A i j.rev
  rw [← sum_fin_reverse (fun i : Fin N => x i.rev*A i j.rev)]
  simp only [Fin.rev_rev]

/-- The inverse triangular transform in the original descending coordinate order. -/
noncomputable def descendingTriangularInverse (η : ℝ) (v : Fin N → 𝕂) :
    Matrix (Fin N) (Fin N) 𝕂 :=
  reverseMatrix (triangularInverseMatrix N (zeroExtendVector (fun i : Fin N => v i.rev))
    (fun j => star (zeroExtendVector (fun i : Fin N => v i.rev) j))
    (fun j => (tailDenominator η (fun i : Fin N => v i.rev) j : 𝕂)))

/-- Permuting both coordinate axes preserves the checked correction bound. -/
theorem descendingTriangularInverse_norm_sq_le (η : ℝ) (hη : 0 < η)
    (v : Fin N → 𝕂) (hv : ∑ i, ‖v i‖^2 = 1) :
    ‖descendingTriangularInverse η v-1‖^2 ≤ 1/(2*η^2) := by
  unfold descendingTriangularInverse
  rw [← reverseMatrix_one, ← reverseMatrix_sub, reverseMatrix_norm_sq]
  apply tail_triangular_inverse_norm_sq_le η hη
  rw [sum_fin_reverse (fun i : Fin N => ‖v i‖^2)]
  exact hv

#print axioms reverseMatrix_norm_sq
#print axioms descendingTriangularInverse_norm_sq_le
end SpectralRadiusUpperTail
