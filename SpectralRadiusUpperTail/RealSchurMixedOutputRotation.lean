import SpectralRadiusUpperTail.RealSchurMixedRotatedJacobian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix Kronecker

/-- Flatten a real matrix with an arbitrary finite coordinate type. -/
def realMatrixEntryEquiv (ι : Type*) [Fintype ι] :
    Matrix ι ι ℝ ≃ₗ[ℝ] (ι × ι → ℝ) where
  toFun X p := X p.1 p.2
  invFun x i j := x (i,j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Two-sided multiplication of real matrices as a real-linear map. -/
def realMatrixTwoSidedMul (ι : Type*) [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) :
    Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℝ where
  toFun X := A*X*B
  map_add' _ _ := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' _ _ := by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl

theorem realMatrixTwoSidedMul_entries (ι : Type*) [Fintype ι] [DecidableEq ι]
    (A B X : Matrix ι ι ℝ) :
    (A ⊗ₖ Bᵀ) *ᵥ realMatrixEntryEquiv ι X =
      realMatrixEntryEquiv ι (A*X*B) := by
  funext p
  change (∑ q : ι × ι, A p.1 q.1 * B q.2 p.2 * X q.1 q.2) = _
  change _ = ∑ k, (∑ j, A p.1 j * X j k) * B k p.2
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_right_comm _ _ _

theorem realMatrixTwoSidedMul_det (ι : Type*) [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) :
    LinearMap.det (realMatrixTwoSidedMul ι A B) =
      A.det ^ Fintype.card ι * B.det ^ Fintype.card ι := by
  have he : (realMatrixEntryEquiv ι).toLinearMap.comp
      ((realMatrixTwoSidedMul ι A B).comp
        (realMatrixEntryEquiv ι).symm.toLinearMap) =
      Matrix.toLin' (A ⊗ₖ Bᵀ) := by
    apply LinearMap.ext
    intro v
    exact (realMatrixTwoSidedMul_entries ι A B
      ((realMatrixEntryEquiv ι).symm v)).symm
  have hd := LinearMap.det_conj (realMatrixTwoSidedMul ι A B)
    (realMatrixEntryEquiv ι)
  rw [he, LinearMap.det_toLin', Matrix.det_kronecker,
    Matrix.det_transpose] at hd
  exact hd.symm

/-- Conjugation by inverse real matrices has determinant one on all
real matrix entries, including mixed block coordinates. -/
theorem realMatrixTwoSidedMul_det_of_inverse
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (hAB : A*B=1) :
    LinearMap.det (realMatrixTwoSidedMul ι A B) = 1 := by
  have hd : A.det * B.det = 1 := by
    rw [← Matrix.det_mul, hAB, Matrix.det_one]
  rw [realMatrixTwoSidedMul_det, ← mul_pow, hd, one_pow]

#print axioms realMatrixTwoSidedMul_det_of_inverse
end SpectralRadiusUpperTail
