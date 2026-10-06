import SpectralRadiusUpperTail.MarkedRealEigenlineRegularFrame
import SpectralRadiusUpperTail.MarkedRealEigenlineRoot
import SpectralRadiusUpperTail.MarkedRealEigenlineScalar
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- Every real characteristic root of a simple-spectrum matrix admits a
regular two-block orthogonal Schur frame whose marked scalar coordinate
is exactly that root. This proves pointwise local coverage, before the
countable-atlas and multiplicity steps in the global density formula. -/
theorem exists_markedRealRoot_regular_frame
    (m : ℕ) (hm : 0 < m)
    (A : Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
      (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ)
    (hsep : A.charpoly.Separable)
    (x : ℝ) (hx : A.charpoly.IsRoot x) :
    ∃ c : RealSchurMixedRegularFrame (markedRealTwoBlockSizes m),
      markedRealScalar m c.T = x ∧
        A = c.Q * c.T * c.Qᵀ := by
  have hchar : A.toEuclideanLin.charpoly = A.charpoly := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    exact Matrix.charpoly_toLin A
      (EuclideanSpace.basisFun (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ).toBasis
  have hx' : A.toEuclideanLin.charpoly.IsRoot x := by
    rw [hchar]
    exact hx
  obtain ⟨v,hv,hAv⟩ :=
    exists_unit_real_eigenvector_of_charpoly_root A.toEuclideanLin x hx'
  obtain ⟨b,c,hb,hcT,hA⟩ :=
    exists_markedRealEigenline_regular_frame m hm A hsep v hv x hAv
  refine ⟨c, ?_, hA⟩
  rw [hcT]
  exact markedRealEigenlineBasis_scalar_eq m A.toEuclideanLin b x
    (by simpa only [hb] using hAv)

#print axioms exists_markedRealRoot_regular_frame
end SpectralRadiusUpperTail
