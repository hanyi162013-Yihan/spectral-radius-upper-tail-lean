import SpectralRadiusUpperTail.MarkedRealGaussianCoordinateTransport
import SpectralRadiusUpperTail.MarkedRealGaussianGlobalArea
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix

/-- The marked real-root count under the actual iid Gaussian matrix law
is exactly the normalized Gaussian integral in mixed entry coordinates. -/
theorem realGaussian_markedRootCount_eq_mixedDensityIntegral
    (m : ℕ) (b : ℝ) :
    (∫⁻ a : (Fin (m+1) × Fin (m+1)) → ℝ,
      markedRealSimpleRootCount m b
        (Matrix.reindex (markedRealIndexEquiv m)
          (markedRealIndexEquiv m) (Matrix.of a.curry))
        ∂gaussianMatrixLaw (m+1)) =
      ∫⁻ y : RealSchurMixedTangent (markedRealTwoBlockSizes m),
        markedRealSimpleRootCount m b
          ((realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y) *
        ENNReal.ofReal
          (realSchurMixedGaussianCoordinateWeight
            (markedRealTwoBlockSizes m) y /
            (Real.sqrt (2*Real.pi))^
              ((Fintype.card
                (RealSchurMixedCoord (markedRealTwoBlockSizes m)))^2))
          ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m) := by
  let H := markedRealGaussianEntryEquiv m
  let f : RealSchurMixedTangent (markedRealTwoBlockSizes m) → ℝ≥0∞ :=
    fun y => markedRealSimpleRootCount m b
      ((realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y)
  have htransport := lintegral_map_equiv
    (μ := gaussianMatrixLaw (m+1)) f H
  rw [gaussianMatrixLaw_map_markedRealGaussianEntryEquiv] at htransport
  have hdensity := gaussianMixedCoordinate_lintegral_density
    (markedRealTwoBlockSizes m) f
  have hpoint (a : (Fin (m+1) × Fin (m+1)) → ℝ) :
      markedRealSimpleRootCount m b
        (Matrix.reindex (markedRealIndexEquiv m)
          (markedRealIndexEquiv m) (Matrix.of a.curry)) = f (H a) := by
    exact congrArg (markedRealSimpleRootCount m b)
      (markedRealGaussianEntryEquiv_matrix m a).symm
  calc
    (∫⁻ a : (Fin (m+1) × Fin (m+1)) → ℝ,
      markedRealSimpleRootCount m b
        (Matrix.reindex (markedRealIndexEquiv m)
          (markedRealIndexEquiv m) (Matrix.of a.curry))
        ∂gaussianMatrixLaw (m+1)) =
      ∫⁻ a, f (H a) ∂gaussianMatrixLaw (m+1) := by
        exact lintegral_congr hpoint
    _ = ∫⁻ y, f y ∂(Measure.pi
      (fun _ : RealSchurMixedCoord (markedRealTwoBlockSizes m) ×
        RealSchurMixedCoord (markedRealTwoBlockSizes m) =>
          standardNormal)).map (realSchurMixedFlatEntryEquiv
            (markedRealTwoBlockSizes m)) := htransport.symm
    _ = _ := by
      rw [hdensity]
      apply lintegral_congr
      intro y
      dsimp [f]
      rw [mul_comm]

#print axioms realGaussian_markedRootCount_eq_mixedDensityIntegral
end SpectralRadiusUpperTail
