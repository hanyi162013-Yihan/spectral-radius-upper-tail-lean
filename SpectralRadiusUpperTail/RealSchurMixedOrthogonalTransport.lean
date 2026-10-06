import SpectralRadiusUpperTail.RealSchurMixedOutputRotation
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- Conjugation by an orthogonal real matrix is an explicit real-linear
equivalence on the full matrix-entry space. -/
noncomputable def realMatrixOrthogonalConjugationEquiv
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℝ) (hQ : Qᵀ*Q=1) :
    Matrix ι ι ℝ ≃ₗ[ℝ] Matrix ι ι ℝ := by
  have hQQ : Q*Qᵀ=1 := mul_eq_one_comm.mp hQ
  exact {
    toFun := fun X => Q*X*Qᵀ
    invFun := fun X => Qᵀ*X*Q
    left_inv := by
      intro X
      calc
        Qᵀ * (Q*X*Qᵀ) * Q = (Qᵀ*Q)*X*(Qᵀ*Q) := by
          simp only [Matrix.mul_assoc]
        _ = X := by simp [hQ]
    right_inv := by
      intro X
      calc
        Q * (Qᵀ*X*Q) * Qᵀ = (Q*Qᵀ)*X*(Q*Qᵀ) := by
          simp only [Matrix.mul_assoc]
        _ = X := by simp [hQQ]
    map_add' := by
      intro X Y
      simp [Matrix.mul_add, Matrix.add_mul]
    map_smul' := by
      intro a X
      simp [Matrix.mul_smul, Matrix.smul_mul] }

/-- This output rotation contributes no absolute-Jacobian factor. -/
theorem realMatrixOrthogonalConjugationEquiv_det
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℝ) (hQ : Qᵀ*Q=1) :
    LinearMap.det (realMatrixOrthogonalConjugationEquiv ι Q hQ).toLinearMap = 1 := by
  have hQQ : Q*Qᵀ=1 := mul_eq_one_comm.mp hQ
  exact realMatrixTwoSidedMul_det_of_inverse ι Q Qᵀ hQQ

#print axioms realMatrixOrthogonalConjugationEquiv_det
end SpectralRadiusUpperTail
