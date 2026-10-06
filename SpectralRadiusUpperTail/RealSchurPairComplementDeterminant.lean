import SpectralRadiusUpperTail.ScalarBridgeBlockDeterminant
import SpectralRadiusUpperTail.RealSchurMixedResultantFactor

namespace SpectralRadiusUpperTail
open scoped Matrix

def realTwoColumnEquiv (m : ℕ) : (Fin m ⊕ Fin m) ≃ (Fin m × Fin 2) where
  toFun
    | .inl i => (i,0)
    | .inr i => (i,1)
  invFun p := if p.2=0 then .inl p.1 else .inr p.1
  left_inv := by intro p; cases p <;> rfl
  right_inv := by rintro ⟨i,j⟩; fin_cases j <;> rfl

theorem realSchurRectangularSylvester_pair_blocks
    (m : ℕ) (H : Matrix (Fin m) (Fin m) ℝ) (B : Matrix (Fin 2) (Fin 2) ℝ) :
    (realSchurRectangularSylvester H B).submatrix (realTwoColumnEquiv m)
      (realTwoColumnEquiv m) =
      Matrix.fromBlocks (H-B 0 0 • 1) ((-B 1 0) • 1)
        ((-B 0 1) • 1) (H-B 1 1 • 1) := by
  ext i j
  cases i <;> cases j <;>
    simp [realTwoColumnEquiv,realSchurRectangularSylvester,Matrix.sub_apply,
      Matrix.smul_apply,Matrix.one_apply]

theorem realSchurPairComplement_quadratic_identity
    (m : ℕ) (H : Matrix (Fin m) (Fin m) ℝ) (B : Matrix (Fin 2) (Fin 2) ℝ) :
    (H-B 1 1 • 1)*(H-B 0 0 • 1)+(B 0 1*(-B 1 0)) • 1 =
      (H-realPairCenter B • 1)^2+realPairHeightSq B • 1 := by
  simp only [realPairHeightSq,realPairCenter,Matrix.trace_fin_two,Matrix.det_fin_two,
    pow_two,Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_smul,Matrix.smul_mul,
    Matrix.mul_one,Matrix.one_mul,smul_sub,smul_smul]
  module

/-- The marked-pair Jacobian reduces to the real quadratic determinant
of the unrestricted complementary matrix. -/
theorem realSchurRectangularSylvester_pair_abs_det
    (m : ℕ) (H : Matrix (Fin m) (Fin m) ℝ) (B : Matrix (Fin 2) (Fin 2) ℝ)
    (hB : B 1 0 ≠ 0) :
    |(realSchurRectangularSylvester H B).det| =
      |((H-realPairCenter B • 1)^2+realPairHeightSq B • 1).det| := by
  rw [← Matrix.det_submatrix_equiv_self (realTwoColumnEquiv m),
    realSchurRectangularSylvester_pair_blocks]
  rw [scalarBridge_block_abs_det _ _ (B 0 1) (-B 1 0) (neg_ne_zero.mpr hB),
    realSchurPairComplement_quadratic_identity]

#print axioms realTwoColumnEquiv
#print axioms realSchurRectangularSylvester_pair_blocks
#print axioms realSchurPairComplement_quadratic_identity
#print axioms realSchurRectangularSylvester_pair_abs_det
end SpectralRadiusUpperTail
