import SpectralRadiusUpperTail.GaussianPrincipalPermutationParseval
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

/-- The Leibniz expansion of a principal minor, expressed in the
Gaussian permutation-word indexing used by the orthogonality theorem. -/
theorem principalMinor_det_eq_gaussianPermutation_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (x : ι × ι → ℝ) :
    ((Matrix.of x.curry).submatrix
      (Subtype.val : s → ι) (Subtype.val : s → ι)).det =
    ∑ π : Equiv.Perm s,
      (((Equiv.Perm.sign π : ℤ) : ℝ) *
        principalPermutationWord (⟨s,π⟩ : PrincipalPermutation ι) x) := by
  let M := (Matrix.of x.curry).submatrix
    (Subtype.val : s → ι) (Subtype.val : s → ι)
  change M.det = _
  rw [← Matrix.det_transpose M, Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro π hπ
  simp [principalPermutationWord, principalPermutationEdge,
    Units.smul_def, M]

#print axioms principalMinor_det_eq_gaussianPermutation_sum
end SpectralRadiusUpperTail
