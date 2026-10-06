import SpectralRadiusUpperTail.MarkedRealStereoImageCount
import SpectralRadiusUpperTail.RealEigenvectorCoordinateNull

namespace SpectralRadiusUpperTail
open MeasureTheory Set
open scoped ENNReal

/-- The global real-root-count identity for the explicit hemisphere.
Only the polynomial coordinate-zero exception is discarded. -/
theorem markedRealStereoRank_lintegral_imageSum_eq_rootCount
    (m : ℕ) (hm : 0 < m) (b : ℝ)
    (g : RealSchurMixedTangent (markedRealTwoBlockSizes m) → ℝ≥0∞)
    (hg : Measurable g) :
    (∑' k : ℕ, ∫⁻ y in markedRealStereoEntryMap m ''
      (markedRealStereoSource m ×ˢ markedRealUpperRankSource m k b),
      g y ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m)) =
      ∫⁻ y, markedRealSimpleRootCount m b
        ((realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y) * g y
          ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m) := by
  let E (k : ℕ) := markedRealStereoEntryMap m ''
    (markedRealStereoSource m ×ˢ markedRealUpperRankSource m k b)
  calc
    _ = ∑' k : ℕ, ∫⁻ y, (E k).indicator g y
        ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m) := by
      congr 1
      funext k
      rw [lintegral_indicator (measurableSet_markedRealStereoRankImage m k hm b)]
    _ = ∫⁻ y, ∑' k : ℕ, (E k).indicator g y
        ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m) := by
      rw [lintegral_tsum]
      intro k
      exact (hg.indicator (measurableSet_markedRealStereoRankImage m k hm b)).aemeasurable
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [markedReal_eigenvectors_nonzero_coordinates_ae m] with y hy
      exact markedRealStereoRank_imageSum_eq_rootCount m hm b g y hy

#print axioms markedRealStereoRank_lintegral_imageSum_eq_rootCount
end SpectralRadiusUpperTail
