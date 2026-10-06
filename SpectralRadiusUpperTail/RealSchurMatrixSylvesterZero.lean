import SpectralRadiusUpperTail.RealSchurCoprimeIntertwiner
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- The rectangular Sylvester equation has only the zero solution when
the characteristic polynomials of the two square matrices are coprime. -/
theorem matrix_eq_zero_of_coprime_charpoly_intertwining
    {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n]
    (A : Matrix m m ℝ) (D : Matrix n n ℝ) (X : Matrix n m ℝ)
    (hcop : IsCoprime A.charpoly D.charpoly)
    (hX : D*X=X*A) :
    X = 0 := by
  have hinter : ∀ v : m → ℝ,
      X.mulVecLin (A.mulVecLin v) =
        D.mulVecLin (X.mulVecLin v) := by
    intro v
    have h := congrArg (fun M : Matrix n m ℝ => M.mulVecLin v) hX
    simpa only [Matrix.mulVecLin_mul, LinearMap.comp_apply] using h.symm
  have hc : IsCoprime A.mulVecLin.charpoly D.mulVecLin.charpoly := by
    simpa only [Matrix.charpoly_mulVecLin] using hcop
  have hzero := linearMap_eq_zero_of_coprime_charpoly_intertwining
    A.mulVecLin D.mulVecLin X.mulVecLin hc hinter
  apply Matrix.ext_of_mulVec_single
  intro j
  have h := LinearMap.congr_fun hzero (Pi.single j 1)
  simpa only [Matrix.mulVecLin_apply, LinearMap.zero_apply,
    Matrix.zero_mulVec] using h

#print axioms matrix_eq_zero_of_coprime_charpoly_intertwining
end SpectralRadiusUpperTail
