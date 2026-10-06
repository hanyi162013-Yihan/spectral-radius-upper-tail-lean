import SpectralRadiusUpperTail.MarkedRealDiagonalNoSpectrumWeight
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix

/-- On a fixed angular chart, summing all real-root ranks gives the
unrestricted scalar/complement Gaussian determinant kernel. -/
theorem markedRealAngularRank_gaussian_area_tsum_kernel
    (m : ℕ) (hm : 0 < m) (b : ℝ) :
    (∑' k : ℕ,
      ∫⁻ y in
        realSchurMixedEntryCoordinates (markedRealTwoBlockSizes m) 0 ''
          (markedRealAngularPositiveSource m ×ˢ
            markedRealUpperRankSource m k b),
        ENNReal.ofReal
          (realSchurMixedGaussianCoordinateWeight
            (markedRealTwoBlockSizes m) y)
          ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m)) =
      (∫⁻ ω, markedRealAngularWeight m ω) *
        (∫⁻ z : ℝ × ((Fin m × Fin m) → ℝ),
          markedRealNoSpectrumDiagonalWeight m b z) := by
  rw [markedRealAngularRank_gaussian_area_tsum m hm b,
    markedRealSimpleDiagonalWeight_lintegral_product m hm b]
  congr 1
  calc
    (∫⁻ z : ℝ × ((Fin m × Fin m) → ℝ),
      markedRealSimpleDiagonalWeight m b
        ((markedRealDiagonalProductEquiv m).symm z)) =
        ∫⁻ z, markedRealExplicitDiagonalWeight m b z := by
      apply lintegral_congr_ae
      exact Filter.Eventually.of_forall
        (markedRealSimpleDiagonalWeight_explicit m hm b)
    _ = ∫⁻ z, markedRealNoSpectrumDiagonalWeight m b z :=
      markedRealExplicitDiagonalWeight_lintegral_noSpectrum m b

#print axioms markedRealAngularRank_gaussian_area_tsum_kernel
end SpectralRadiusUpperTail
