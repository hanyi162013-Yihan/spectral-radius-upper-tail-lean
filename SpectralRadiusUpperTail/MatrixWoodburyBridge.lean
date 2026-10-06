import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace SpectralRadiusUpperTail
open scoped Matrix
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

lemma matrix_sub_mul_isUnit (A : Matrix n n ℂ) (U : Matrix n ι ℂ) (V : Matrix ι n ℂ)
    (hA : IsUnit A) (hB : IsUnit (1-V*A⁻¹*U)) : IsUnit (A-U*V) := by
  obtain ⟨iA⟩ := hA.nonempty_invertible
  letI : Invertible (1 : Matrix ι ι ℂ) := invertibleOne
  have hAC : IsUnit ((1 : Matrix ι ι ℂ)⁻¹+V*A⁻¹*(-U)) := by
    simpa only [inv_one,Matrix.mul_neg,sub_eq_add_neg] using hB
  obtain ⟨iAC⟩ := hAC.nonempty_invertible
  simp only [← Matrix.invOf_eq_nonsing_inv] at iAC
  letI := Matrix.invertibleAddMulMul A (-U) (1 : Matrix ι ι ℂ) V
  simpa only [Matrix.mul_one,Matrix.neg_mul,sub_eq_add_neg] using (isUnit_of_invertible (A+(-U)*(1 : Matrix ι ι ℂ)*V))

lemma matrix_sub_mul_inverse (A : Matrix n n ℂ) (U : Matrix n ι ℂ) (V : Matrix ι n ℂ)
    (hA : IsUnit A) (hB : IsUnit (1-V*A⁻¹*U)) :
    (A-U*V)⁻¹ = A⁻¹+A⁻¹*U*(1-V*A⁻¹*U)⁻¹*V*A⁻¹ := by
  have hAC : IsUnit ((1 : Matrix ι ι ℂ)⁻¹+V*A⁻¹*(-U)) := by
    simpa only [inv_one,Matrix.mul_neg,sub_eq_add_neg] using hB
  have hh := Matrix.add_mul_mul_inv_eq_sub A (-U) (1 : Matrix ι ι ℂ) V hA isUnit_one hAC
  simpa only [inv_one,Matrix.mul_one,Matrix.mul_neg,Matrix.neg_mul,
    sub_neg_eq_add,← sub_eq_add_neg] using hh

#print axioms matrix_sub_mul_isUnit
#print axioms matrix_sub_mul_inverse
end SpectralRadiusUpperTail
