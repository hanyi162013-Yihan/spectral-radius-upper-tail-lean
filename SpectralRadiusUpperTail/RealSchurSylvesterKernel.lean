import SpectralRadiusUpperTail.RealSchurMatrixSylvesterZero
import SpectralRadiusUpperTail.RealSchurMixedSylvesterFactors

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

theorem realSchurRectangularSylvester_mulVec
    {a b : ℕ} (D : Matrix (Fin a) (Fin a) ℝ)
    (E : Matrix (Fin b) (Fin b) ℝ) (w : Fin a × Fin b → ℝ)
    (i : Fin a) (j : Fin b) :
    (realSchurRectangularSylvester D E).mulVec w (i,j) =
      (D * Matrix.of w.curry - Matrix.of w.curry * E) i j := by
  simp only [Matrix.mulVec, dotProduct, realSchurRectangularSylvester,
    sub_mul, Finset.sum_sub_distrib, Fintype.sum_prod_type,
    ite_mul, zero_mul, Matrix.sub_apply, Matrix.mul_apply, Matrix.of_apply,
    Function.curry]
  simp [mul_comm]

theorem realSchurRectangularSylvester_kernel_eq_zero
    {a b : ℕ} (D : Matrix (Fin a) (Fin a) ℝ)
    (E : Matrix (Fin b) (Fin b) ℝ)
    (hcop : IsCoprime D.charpoly E.charpoly)
    (w : Fin a × Fin b → ℝ)
    (hw : (realSchurRectangularSylvester D E).mulVec w=0) : w=0 := by
  have hmat : D * Matrix.of w.curry = Matrix.of w.curry * E := by
    ext i j
    have h := congrFun hw (i,j)
    rw [realSchurRectangularSylvester_mulVec] at h
    exact sub_eq_zero.mp h
  have hzero := matrix_eq_zero_of_coprime_charpoly_intertwining
    E D (Matrix.of w.curry) hcop.symm hmat
  funext p
  exact congrFun (congrFun hzero p.1) p.2

/-- Arbitrary block sizes are allowed here. The marked nonreal block has
size two, but its complementary block is not restricted to size two. -/
theorem realSchurRectangularSylvester_ne_zero_of_coprime
    {a b : ℕ} (D : Matrix (Fin a) (Fin a) ℝ)
    (E : Matrix (Fin b) (Fin b) ℝ)
    (hcop : IsCoprime D.charpoly E.charpoly) :
    (realSchurRectangularSylvester D E).det ≠ 0 := by
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  apply sub_eq_zero.mp
  apply realSchurRectangularSylvester_kernel_eq_zero D E hcop
  rw [Matrix.mulVec_sub,hxy,sub_self]

#print axioms realSchurRectangularSylvester_mulVec
#print axioms realSchurRectangularSylvester_kernel_eq_zero
#print axioms realSchurRectangularSylvester_ne_zero_of_coprime
end SpectralRadiusUpperTail
