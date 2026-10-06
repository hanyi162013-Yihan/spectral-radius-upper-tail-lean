import SpectralRadiusUpperTail.MarkedRealChartImageCount
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

/-- The countable marked atlas converts overlapping matrix images into
the exact real-root multiplicity on the simple-spectrum locus. -/
theorem markedRealChart_lintegral_imageSum_eq_rootCount
    (m : ℕ) (hm : 0 < m) (b : ℝ)
    (c : ℕ → RealSchurMixedRegularFrame (markedRealTwoBlockSizes m))
    (hcover :
      (⋃ k, markedRealIncidenceFirstPatch m b c k) = Set.univ)
    (g : RealSchurMixedTangent (markedRealTwoBlockSizes m) → ℝ≥0∞)
    (hg : Measurable g) :
    (∑' k, ∫⁻ y in markedRealChartEntryImage m b c k,
      g y ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m)) =
      ∫⁻ y,
        markedRealSimpleRootCount m b
          ((realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y) *
        g y ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m) := by
  have hsum (y : RealSchurMixedTangent (markedRealTwoBlockSizes m)) :
      (∑' k, (markedRealChartEntryImage m b c k).indicator g y) =
        markedRealSimpleRootCount m b
          ((realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y) * g y := by
    let I : Set ℕ := {k | y ∈ markedRealChartEntryImage m b c k}
    have hone :
        (∑' k, (markedRealChartEntryImage m b c k).indicator
          (fun _ => (1 : ℝ≥0∞)) y) = (I.encard : ℝ≥0∞) := by
      calc
        (∑' k, (markedRealChartEntryImage m b c k).indicator
          (fun _ => (1 : ℝ≥0∞)) y) =
            ∑' k, I.indicator (fun _ => (1 : ℝ≥0∞)) k := by
          congr 1
        _ = ∑' k : I, (1 : ℝ≥0∞) := (tsum_subtype I 1).symm
        _ = (I.encard : ℝ≥0∞) := ENNReal.tsum_set_one I
    calc
      (∑' k, (markedRealChartEntryImage m b c k).indicator g y) =
          ∑' k, (markedRealChartEntryImage m b c k).indicator
            (fun _ => (1 : ℝ≥0∞)) y * g y := by
        congr 1
        funext k
        by_cases hk : y ∈ markedRealChartEntryImage m b c k <;>
          simp [indicator, hk]
      _ = (∑' k, (markedRealChartEntryImage m b c k).indicator
          (fun _ => (1 : ℝ≥0∞)) y) * g y :=
        ENNReal.tsum_mul_right
      _ = markedRealSimpleRootCount m b
          ((realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y) *
          g y := by
        rw [hone]
        congr 1
        simpa only [I, markedRealSimpleRootCount] using
          congrArg (fun q : ℕ∞ => (q : ℝ≥0∞))
            (markedRealChart_entryImage_encard m hm b c hcover y)
  calc
    (∑' k, ∫⁻ y in markedRealChartEntryImage m b c k,
      g y ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m)) =
        ∑' k, ∫⁻ y,
          (markedRealChartEntryImage m b c k).indicator g y
            ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m) := by
      congr 1
      funext k
      rw [lintegral_indicator
        (measurableSet_markedRealChartEntryImage m b c k)]
    _ = ∫⁻ y, ∑' k,
        (markedRealChartEntryImage m b c k).indicator g y
          ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m) := by
      rw [lintegral_tsum]
      intro k
      exact (hg.indicator
        (measurableSet_markedRealChartEntryImage m b c k)).aemeasurable
    _ = ∫⁻ y,
        markedRealSimpleRootCount m b
          ((realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y) *
        g y ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m) := by
      congr 1
      funext y
      exact hsum y

#print axioms markedRealChart_lintegral_imageSum_eq_rootCount
end SpectralRadiusUpperTail
