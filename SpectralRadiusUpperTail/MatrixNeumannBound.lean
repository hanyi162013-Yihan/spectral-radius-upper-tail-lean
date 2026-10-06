import SpectralRadiusUpperTail.ResolventPerturbation
import SpectralRadiusUpperTail.FiniteMatrixEntryBound
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma finite_matrix_norm_one_le : ‖(1 : Matrix ι ι ℂ)‖ ≤ 1 := by
  rw [← Matrix.diagonal_one,Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr (by simp)

lemma matrix_neumann_inverse_bound (B : Matrix ι ι ℂ) (hB : ‖B‖ ≤ 1/2) :
    IsUnit (1-B) ∧ ‖(1-B)⁻¹‖ ≤ 2 := by
  have hu : IsUnit (1-B) := isUnit_one_sub_of_norm_lt_one (by linarith)
  refine ⟨hu,?_⟩
  have hi : (1-B)⁻¹-B*(1-B)⁻¹ = 1 := by
    have hh := Ring.mul_inverse_cancel (1-B) hu
    rw [← Matrix.nonsing_inv_eq_ringInverse,Matrix.sub_mul,Matrix.one_mul] at hh
    exact hh
  have he : (1-B)⁻¹ = 1+B*(1-B)⁻¹ := (sub_eq_iff_eq_add).mp hi
  have hn := norm_add_le (1 : Matrix ι ι ℂ) (B*(1-B)⁻¹)
  rw [← he] at hn
  have hm := norm_mul_le B ((1-B)⁻¹)
  have hs := mul_le_mul_of_nonneg_right hB (norm_nonneg ((1-B)⁻¹))
  have h1 : ‖(1 : Matrix ι ι ℂ)‖ ≤ 1 := finite_matrix_norm_one_le
  nlinarith

#print axioms finite_matrix_norm_one_le
#print axioms matrix_neumann_inverse_bound
end SpectralRadiusUpperTail
