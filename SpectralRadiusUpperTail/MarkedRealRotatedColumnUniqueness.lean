import SpectralRadiusUpperTail.MarkedRealUpperEigenvector
import SpectralRadiusUpperTail.MarkedRealOrthogonalColumnSign
import SpectralRadiusUpperTail.MarkedRealEigenlineMultiplicity
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- For a simple-spectrum matrix, two block-upper representations of the
same marked eigenvalue have the same first orthogonal column once its
sign is fixed. This holds without ordering the complementary spectrum. -/
theorem markedRealUpper_rotatedColumns_eq_of_sameRoot
    (m : ℕ)
    (A Q R S T : Matrix
      (RealSchurMixedCoord (markedRealTwoBlockSizes m))
      (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ)
    (hsep : A.charpoly.Separable)
    (hS : realSchurMixedLowerProjection (markedRealTwoBlockSizes m) S = 0)
    (hT : realSchurMixedLowerProjection (markedRealTwoBlockSizes m) T = 0)
    (hQ : Qᵀ*Q=1) (hR : Rᵀ*R=1)
    (hAQ : A=Q*S*Qᵀ) (hAR : A=R*T*Rᵀ)
    (hscalar : markedRealScalar m S = markedRealScalar m T)
    (hQpos : 0 < Q (markedRealFirstCoordinate m)
      (markedRealFirstCoordinate m))
    (hRpos : 0 < R (markedRealFirstCoordinate m)
      (markedRealFirstCoordinate m)) :
    ∀ i, Q i (markedRealFirstCoordinate m) =
      R i (markedRealFirstCoordinate m) := by
  let e := markedRealFirstCoordinate m
  let v := Q.mulVecLin (Pi.single e 1)
  let w := R.mulVecLin (Pi.single e 1)
  have hv : v ≠ 0 := by
    intro hz
    have he := congrFun hz e
    have heq : v e = Q e e := by
      simp [v, Matrix.mulVecLin_apply]
    rw [heq] at he
    simp at he
    exact (ne_of_gt hQpos) he
  have hfv : A.mulVecLin v = markedRealScalar m S • v := by
    rw [hAQ]
    exact markedRealUpper_rotatedFirstColumn_eigenvector m S Q hS hQ
  have hfw : A.mulVecLin w = markedRealScalar m S • w := by
    rw [hAR, hscalar]
    exact markedRealUpper_rotatedFirstColumn_eigenvector m T R hT hR
  obtain ⟨c,hc⟩ := real_eigenvectors_collinear_of_separable
    A.mulVecLin (by simpa only [Matrix.charpoly_mulVecLin] using hsep)
      (markedRealScalar m S) v w hv hfv hfw
  have hcol (i) : R i e = c * Q i e := by
    have hi := congrFun hc i
    simpa [v, w, Matrix.mulVecLin_apply, Pi.smul_apply] using hi.symm
  have h := orthogonal_firstColumns_eq_of_collinear_positive
    e Q R hQ hR c hcol hQpos hRpos
  intro i
  exact (h i).symm

#print axioms markedRealUpper_rotatedColumns_eq_of_sameRoot
end SpectralRadiusUpperTail
