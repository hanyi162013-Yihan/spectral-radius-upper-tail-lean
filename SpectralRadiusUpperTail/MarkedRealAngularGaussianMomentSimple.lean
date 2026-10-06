import SpectralRadiusUpperTail.MarkedRealGaussianMomentNormalizer
import SpectralRadiusUpperTail.MarkedRealGaussianCharpolyMomentBounds
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix

/-- The fixed-chart formula with its Gaussian partition function in
the compact m²+m form. -/
theorem markedRealAngularRank_gaussian_area_tsum_moment_simple
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
        (∫⁻ x : ℝ,
          if b < x then
            ENNReal.ofReal (Real.exp (-x^2/2)) *
              ENNReal.ofReal ((Real.sqrt (2*Real.pi))^(m^2+m)) *
              markedRealGaussianCharpolyMoment m x
          else 0) := by
  rw [markedRealAngularRank_gaussian_area_tsum_moment m hm b]
  congr 1
  apply lintegral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    by_cases hb : b < x
    · simp only [if_pos hb]
      rw [show m^2+m = m+m^2 by omega]
      rw [← markedRealTwoBlock_gaussianNormalizer_product m]
      ac_rfl
    · simp only [if_neg hb])

#print axioms markedRealAngularRank_gaussian_area_tsum_moment_simple
end SpectralRadiusUpperTail
