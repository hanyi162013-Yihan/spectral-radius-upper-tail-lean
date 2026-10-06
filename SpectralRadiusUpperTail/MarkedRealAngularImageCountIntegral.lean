import SpectralRadiusUpperTail.MarkedRealAngularImageCountBound
import SpectralRadiusUpperTail.MarkedRealAngularImageMeasurable
import SpectralRadiusUpperTail.MarkedRealChartImageCount
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

/-- Summing the fixed-angle rank images cannot exceed the genuine
real-root-count integral. -/
theorem markedRealAngularRank_lintegral_imageSum_le_rootCount
    (m : ℕ) (hm : 0 < m) (b : ℝ)
    (g : RealSchurMixedTangent (markedRealTwoBlockSizes m) → ℝ≥0∞)
    (hg : Measurable g) :
    (∑' k, ∫⁻ y in
      realSchurMixedEntryCoordinates (markedRealTwoBlockSizes m) 0 ''
        (markedRealAngularPositiveSource m ×ˢ
          markedRealUpperRankSource m k b),
      g y ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m)) ≤
      ∫⁻ y,
        markedRealSimpleRootCount m b
          ((realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y) *
        g y ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m) := by
  let E (k : ℕ) : Set (RealSchurMixedTangent (markedRealTwoBlockSizes m)) :=
    realSchurMixedEntryCoordinates (markedRealTwoBlockSizes m) 0 ''
      (markedRealAngularPositiveSource m ×ˢ
        markedRealUpperRankSource m k b)
  have hsum (y : RealSchurMixedTangent (markedRealTwoBlockSizes m)) :
      (∑' k, (E k).indicator g y) ≤
        markedRealSimpleRootCount m b
          ((realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y) * g y := by
    let I : Set ℕ := {k | y ∈ E k}
    have hone :
        (∑' k, (E k).indicator (fun _ => (1 : ℝ≥0∞)) y) =
          (I.encard : ℝ≥0∞) := by
      calc
        (∑' k, (E k).indicator (fun _ => (1 : ℝ≥0∞)) y) =
            ∑' k, I.indicator (fun _ => (1 : ℝ≥0∞)) k := by
          congr 1
        _ = ∑' k : I, (1 : ℝ≥0∞) := (tsum_subtype I 1).symm
        _ = (I.encard : ℝ≥0∞) := ENNReal.tsum_set_one I
    calc
      (∑' k, (E k).indicator g y) =
          ∑' k, (E k).indicator (fun _ => (1 : ℝ≥0∞)) y * g y := by
        congr 1
        funext k
        by_cases hk : y ∈ E k <;> simp [indicator, hk]
      _ = (I.encard : ℝ≥0∞) * g y := by
        rw [ENNReal.tsum_mul_right, hone]
      _ ≤ markedRealSimpleRootCount m b
          ((realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y) *
          g y := by
        gcongr
        change (I.encard : ℝ≥0∞) ≤
          ({x : ℝ |
            ((realSchurMixedEntryEquiv
              (markedRealTwoBlockSizes m)).symm y).charpoly.Separable ∧
            ((realSchurMixedEntryEquiv
              (markedRealTwoBlockSizes m)).symm y).charpoly.IsRoot x ∧
            b < x}.encard : ℝ≥0∞)
        exact_mod_cast markedRealAngularRank_image_encard_le_root_encard
          m hm b y
  calc
    (∑' k, ∫⁻ y in E k,
      g y ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m)) =
        ∑' k, ∫⁻ y, (E k).indicator g y
          ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m) := by
      congr 1
      funext k
      rw [lintegral_indicator
        (measurableSet_markedRealAngularRankImage m k hm b)]
    _ = ∫⁻ y, ∑' k, (E k).indicator g y
        ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m) := by
      rw [lintegral_tsum]
      intro k
      exact (hg.indicator
        (measurableSet_markedRealAngularRankImage m k hm b)).aemeasurable
    _ ≤ ∫⁻ y,
        markedRealSimpleRootCount m b
          ((realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y) *
          g y ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m) :=
      lintegral_mono hsum

#print axioms markedRealAngularRank_lintegral_imageSum_le_rootCount
end SpectralRadiusUpperTail
