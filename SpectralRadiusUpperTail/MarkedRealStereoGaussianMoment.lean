import SpectralRadiusUpperTail.MarkedRealStereoGaussianFactor
import SpectralRadiusUpperTail.MarkedRealAngularGaussianMomentSimple

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix BigOperators

/- Exact Gaussian integration over the explicit hemisphere, reusing the
checked upper-row and complementary-matrix integration. Identification
with the complete actual root count is a separate coverage step. -/

theorem markedRealStereoRank_gaussian_area_tsum
    (m : ℕ) (hm : 0 < m) (b : ℝ) :
    (∑' k : ℕ,
      ∫⁻ y in
        markedRealStereoEntryMap m ''
          (markedRealStereoSource m ×ˢ
            markedRealUpperRankSource m k b),
        ENNReal.ofReal
          (realSchurMixedGaussianCoordinateWeight
            (markedRealTwoBlockSizes m) y)
          ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m)) =
      (∫⁻ ω, markedRealStereoAngularWeight m ω) *
        (∫⁻ d, markedRealSimpleDiagonalWeight m b d) := by
  simp_rw [markedRealStereoRank_gaussian_factor m _ hm b,
    markedRealRankRestWeight_lintegral_diagonal m _ hm b]
  rw [ENNReal.tsum_mul_left,
    markedRealRankDiagonalWeight_lintegral_tsum m hm b]


theorem markedRealStereoRank_gaussian_area_tsum_kernel
    (m : ℕ) (hm : 0 < m) (b : ℝ) :
    (∑' k : ℕ,
      ∫⁻ y in
        markedRealStereoEntryMap m ''
          (markedRealStereoSource m ×ˢ
            markedRealUpperRankSource m k b),
        ENNReal.ofReal
          (realSchurMixedGaussianCoordinateWeight
            (markedRealTwoBlockSizes m) y)
          ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m)) =
      (∫⁻ ω, markedRealStereoAngularWeight m ω) *
        (∫⁻ z : ℝ × ((Fin m × Fin m) → ℝ),
          markedRealNoSpectrumDiagonalWeight m b z) := by
  rw [markedRealStereoRank_gaussian_area_tsum m hm b,
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


theorem markedRealStereoRank_gaussian_area_tsum_charpoly
    (m : ℕ) (hm : 0 < m) (b : ℝ) :
    (∑' k : ℕ,
      ∫⁻ y in
        markedRealStereoEntryMap m ''
          (markedRealStereoSource m ×ˢ
            markedRealUpperRankSource m k b),
        ENNReal.ofReal
          (realSchurMixedGaussianCoordinateWeight
            (markedRealTwoBlockSizes m) y)
          ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m)) =
      (∫⁻ ω, markedRealStereoAngularWeight m ω) *
        (∫⁻ x : ℝ, ∫⁻ a : (Fin m × Fin m) → ℝ,
          markedRealCharpolyKernel m b x a) := by
  rw [markedRealStereoRank_gaussian_area_tsum_kernel m hm b,
    markedRealNoSpectrumDiagonalWeight_lintegral_prod m b]
  congr 1
  apply lintegral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    apply lintegral_congr_ae
    exact Filter.Eventually.of_forall
      (markedRealNoSpectrumDiagonalWeight_eq_charpoly m b x))


theorem markedRealStereoRank_gaussian_area_tsum_moment
    (m : ℕ) (hm : 0 < m) (b : ℝ) :
    (∑' k : ℕ,
      ∫⁻ y in
        markedRealStereoEntryMap m ''
          (markedRealStereoSource m ×ˢ
            markedRealUpperRankSource m k b),
        ENNReal.ofReal
          (realSchurMixedGaussianCoordinateWeight
            (markedRealTwoBlockSizes m) y)
          ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m)) =
      (∫⁻ ω, markedRealStereoAngularWeight m ω) *
        (∫⁻ x : ℝ,
          if b < x then
            ENNReal.ofReal (Real.exp (-x^2/2)) *
              ENNReal.ofReal ((Real.sqrt (2*Real.pi)) ^
                (Fintype.card
                  (RealSchurMixedStrictUpperEntry
                    (markedRealTwoBlockSizes m)))) *
              ENNReal.ofReal ((Real.sqrt (2*Real.pi))^(m^2)) *
              markedRealGaussianCharpolyMoment m x
          else 0) := by
  rw [markedRealStereoRank_gaussian_area_tsum_charpoly m hm b]
  congr 1
  apply lintegral_congr_ae
  exact Filter.Eventually.of_forall
    (fun x => markedRealCharpolyKernel_lintegral_complement m b x)


theorem markedRealStereoRank_gaussian_area_tsum_moment_simple
    (m : ℕ) (hm : 0 < m) (b : ℝ) :
    (∑' k : ℕ,
      ∫⁻ y in
        markedRealStereoEntryMap m ''
          (markedRealStereoSource m ×ˢ
            markedRealUpperRankSource m k b),
        ENNReal.ofReal
          (realSchurMixedGaussianCoordinateWeight
            (markedRealTwoBlockSizes m) y)
          ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m)) =
      (∫⁻ ω, markedRealStereoAngularWeight m ω) *
        (∫⁻ x : ℝ,
          if b < x then
            ENNReal.ofReal (Real.exp (-x^2/2)) *
              ENNReal.ofReal ((Real.sqrt (2*Real.pi))^(m^2+m)) *
              markedRealGaussianCharpolyMoment m x
          else 0) := by
  rw [markedRealStereoRank_gaussian_area_tsum_moment m hm b]
  congr 1
  apply lintegral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    by_cases hb : b < x
    · simp only [if_pos hb]
      rw [show m^2+m = m+m^2 by omega]
      rw [← markedRealTwoBlock_gaussianNormalizer_product m]
      ac_rfl
    · simp only [if_neg hb])

#print axioms markedRealStereoRank_gaussian_area_tsum
#print axioms markedRealStereoRank_gaussian_area_tsum_kernel
#print axioms markedRealStereoRank_gaussian_area_tsum_charpoly
#print axioms markedRealStereoRank_gaussian_area_tsum_moment
#print axioms markedRealStereoRank_gaussian_area_tsum_moment_simple
end SpectralRadiusUpperTail
