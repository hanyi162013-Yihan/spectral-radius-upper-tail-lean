import SpectralRadiusUpperTail.MarkedRealStereoRankImage
import SpectralRadiusUpperTail.MarkedRealChartImageCount

namespace SpectralRadiusUpperTail
open Set MeasureTheory
open scoped ENNReal

/-- Outside the coordinate-zero exception, the rank images count each
simple real root above the cutoff exactly once. -/
theorem markedRealStereoRank_image_encard (m : ℕ) (hm : 0 < m) (b : ℝ)
    (y : RealSchurMixedTangent (markedRealTwoBlockSizes m))
    (hcoord : realMatrixEigenvectorsHaveNonzeroCoordinates
      (RealSchurMixedCoord (markedRealTwoBlockSizes m))
      ((realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y)) :
    {k : ℕ | y ∈ markedRealStereoEntryMap m ''
      (markedRealStereoSource m ×ˢ markedRealUpperRankSource m k b)}.encard =
      {z : ℝ |
        ((realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y).charpoly.Separable ∧
        ((realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y).charpoly.IsRoot z ∧
        b < z}.encard := by
  let A := (realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y
  let R : Set ℝ := {z | A.charpoly.Separable ∧ A.charpoly.IsRoot z ∧ b < z}
  let f : ℝ → ℕ := realPolynomialRootRank A.charpoly
  have heq : {k : ℕ | y ∈ markedRealStereoEntryMap m ''
      (markedRealStereoSource m ×ˢ markedRealUpperRankSource m k b)} = f '' R := by
    ext k
    constructor
    · intro hk
      obtain ⟨hsep,z,hz,hb,hr⟩ := markedRealStereoRank_image_has_rankedRoot m k hm b y hk
      exact ⟨z, ⟨hsep,hz,hb⟩, hr⟩
    · rintro ⟨z,hz,hr⟩
      rw [← hr]
      exact markedRealStereoRank_mem_image_of_root m b z y hcoord hz.1 hz.2.1 hz.2.2
  have hinj : InjOn f R := by
    intro z hz t ht he
    exact realPolynomialRootRank_injective_on_roots A.charpoly A.charpoly_monic.ne_zero
      z t hz.2.1 ht.2.1 he
  rw [heq]
  exact hinj.encard_image

theorem markedRealStereoRank_imageSum_eq_rootCount (m : ℕ) (hm : 0 < m) (b : ℝ)
    (g : RealSchurMixedTangent (markedRealTwoBlockSizes m) → ℝ≥0∞)
    (y : RealSchurMixedTangent (markedRealTwoBlockSizes m))
    (hcoord : realMatrixEigenvectorsHaveNonzeroCoordinates
      (RealSchurMixedCoord (markedRealTwoBlockSizes m))
      ((realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y)) :
    (∑' k : ℕ, (markedRealStereoEntryMap m ''
      (markedRealStereoSource m ×ˢ markedRealUpperRankSource m k b)).indicator g y) =
      markedRealSimpleRootCount m b
        ((realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y) * g y := by
  let E (k : ℕ) := markedRealStereoEntryMap m ''
    (markedRealStereoSource m ×ˢ markedRealUpperRankSource m k b)
  let I : Set ℕ := {k | y ∈ E k}
  have hone : (∑' k : ℕ, (E k).indicator (fun _ => (1 : ℝ≥0∞)) y) =
      (I.encard : ℝ≥0∞) := by
    calc
      _ = ∑' k : ℕ, I.indicator (fun _ => (1 : ℝ≥0∞)) k := by congr 1
      _ = ∑' k : I, (1 : ℝ≥0∞) := (tsum_subtype I 1).symm
      _ = _ := ENNReal.tsum_set_one I
  calc
    _ = ∑' k, (E k).indicator (fun _ => (1 : ℝ≥0∞)) y * g y := by
      congr 1
      funext k
      by_cases hk : y ∈ E k <;> simp [E, indicator, hk]
    _ = (I.encard : ℝ≥0∞) * g y := by rw [ENNReal.tsum_mul_right, hone]
    _ = _ := by
      congr 1
      exact congrArg (fun t : ℕ∞ => (t : ℝ≥0∞))
        (markedRealStereoRank_image_encard m hm b y hcoord)

#print axioms markedRealStereoRank_image_encard
#print axioms markedRealStereoRank_imageSum_eq_rootCount
end SpectralRadiusUpperTail
