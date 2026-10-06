import SpectralRadiusUpperTail.MarkedRealEigenlineBlockUpper
import SpectralRadiusUpperTail.MarkedRealTwoBlockGaussianChart
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- The scalar diagonal coordinate of an adapted eigenline basis is the
marked real eigenvalue itself. -/
theorem markedRealEigenlineBasis_scalar_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (m : ℕ)
    (f : E →ₗ[ℝ] E) (b : OrthonormalBasis
      (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ E)
    (x : ℝ)
    (hf : f (b (markedRealFirstCoordinate m)) =
      x • b (markedRealFirstCoordinate m)) :
    markedRealScalar m (LinearMap.toMatrix b.toBasis b.toBasis f) = x := by
  change (LinearMap.toMatrix b.toBasis b.toBasis f)
    (markedRealFirstCoordinate m) (markedRealFirstCoordinate m) = x
  rw [LinearMap.toMatrix_apply, b.coe_toBasis_repr_apply]
  change b.repr (f (b (markedRealFirstCoordinate m)))
    (markedRealFirstCoordinate m) = x
  rw [hf, map_smul]
  simp [OrthonormalBasis.repr_self]

#print axioms markedRealEigenlineBasis_scalar_eq
end SpectralRadiusUpperTail
