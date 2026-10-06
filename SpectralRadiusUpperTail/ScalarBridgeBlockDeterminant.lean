import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- An off-diagonal scalar block permits a Schur determinant reduction
without assuming that either large diagonal block is invertible. -/
theorem scalarBridge_block_abs_det
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A D : Matrix ι ι ℝ) (b c : ℝ) (hc : c ≠ 0) :
    |(Matrix.fromBlocks A (c • 1) ((-b) • 1) D).det| =
      |(D*A+(b*c) • 1).det| := by
  let M := Matrix.fromBlocks A (c • 1) ((-b) • 1) D
  have hswap : M.submatrix (Equiv.refl (ι ⊕ ι)) (Equiv.sumComm ι ι) =
      Matrix.fromBlocks (c • 1) A D ((-b) • 1) := by
    ext i j
    cases i <;> cases j <;> rfl
  have hfac : Matrix.fromBlocks (c • (1 : Matrix ι ι ℝ)) A D ((-b) • 1) =
      Matrix.fromBlocks (c • (1 : Matrix ι ι ℝ)) 0 0 1 *
        Matrix.fromBlocks 1 (c⁻¹ • A) D ((-b) • 1) := by
    rw [Matrix.fromBlocks_multiply]
    simp [Matrix.smul_mul,Matrix.mul_smul,smul_smul,hc]
  have hinner : (c • (1 : Matrix ι ι ℝ)) *
      ((-b) • 1 - D*(c⁻¹ • A)) = -(D*A+(b*c) • 1) := by
    rw [Matrix.smul_mul,Matrix.one_mul,smul_sub,Matrix.mul_smul,
      smul_smul,smul_smul,mul_inv_cancel₀ hc,one_smul]
    module
  calc
    |M.det| = |(M.submatrix (Equiv.refl (ι ⊕ ι)) (Equiv.sumComm ι ι)).det| :=
      (Matrix.abs_det_submatrix_equiv_equiv _ _ M).symm
    _ = |(Matrix.fromBlocks (c • (1 : Matrix ι ι ℝ)) A D ((-b) • 1)).det| := by rw [hswap]
    _ = |(c • (1 : Matrix ι ι ℝ)).det * ((-b) • 1-D*(c⁻¹ • A)).det| := by
      rw [hfac,Matrix.det_mul,Matrix.det_fromBlocks_zero₂₁,
        Matrix.det_one,mul_one,Matrix.det_fromBlocks_one₁₁]
    _ = |(-(D*A+(b*c) • 1)).det| := by rw [← Matrix.det_mul,hinner]
    _ = |(D*A+(b*c) • 1).det| := by rw [Matrix.det_neg,abs_mul,abs_pow]; simp

#print axioms scalarBridge_block_abs_det
end SpectralRadiusUpperTail
