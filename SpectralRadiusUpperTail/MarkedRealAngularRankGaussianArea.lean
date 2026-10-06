import SpectralRadiusUpperTail.MarkedRealAngularRankMeasurable
import SpectralRadiusUpperTail.RealSchurMixedGaussianLocalIntegration
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix

/-- On every complete measurable rank layer, the matrix Gaussian
integral equals a product-coordinate integral whose density is independent
of the angular variable except for the explicit angular Jacobian. -/
theorem markedRealAngularRank_gaussianArea
    (m k : ℕ) (hm : 0 < m) (b : ℝ) :
    (∫⁻ y in
      realSchurMixedEntryCoordinates (markedRealTwoBlockSizes m) 0 ''
        (markedRealAngularPositiveSource m ×ˢ
          markedRealUpperRankSource m k b),
      ENNReal.ofReal
        (realSchurMixedGaussianCoordinateWeight
          (markedRealTwoBlockSizes m) y)
        ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m)) =
    ∫⁻ x in (markedRealAngularPositiveSource m ×ˢ
        markedRealUpperRankSource m k b),
      ENNReal.ofReal (
        |(markedRealComplement m x.2.val -
            markedRealScalar m x.2.val •
              (1 : Matrix (Fin m) (Fin m) ℝ)).det| *
          |realSchurMixedAngularJacobian
            (markedRealTwoBlockSizes m) x.1|) *
        ENNReal.ofReal (realMatrixGaussianWeight
          (RealSchurMixedCoord (markedRealTwoBlockSizes m)) x.2.val)
        ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m) := by
  rw [markedRealAngularRank_lintegral_full m k hm b
    (fun y => ENNReal.ofReal
      (realSchurMixedGaussianCoordinateWeight
        (markedRealTwoBlockSizes m) y))]
  apply lintegral_congr
  intro x
  rw [realSchurMixedGaussianCoordinateWeight_chart
    (markedRealTwoBlockSizes m) 0 x]
  simp

#print axioms markedRealAngularRank_gaussianArea
end SpectralRadiusUpperTail
