import SpectralRadiusUpperTail.MarkedRealStereoGaussianCount
import SpectralRadiusUpperTail.MarkedRealGaussianExpectationBridge
import SpectralRadiusUpperTail.MarkedRealAngularNormalizerRatio

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix

/-- Exact actual-law count identity with only the first-column Gaussian
normalizer left. The complementary determinant moment is under an iid
standard real Gaussian law. -/
theorem realGaussian_markedRootCount_stereo_moment
    (m : ℕ) (hm : 0 < m) (b : ℝ) :
    (∫⁻ a : (Fin (m+1) × Fin (m+1)) → ℝ,
      markedRealSimpleRootCount m b
        (Matrix.reindex (markedRealIndexEquiv m)
          (markedRealIndexEquiv m) (Matrix.of a.curry))
        ∂gaussianMatrixLaw (m+1)) =
      (∫⁻ w, markedRealStereoAngularWeight m w) *
        (∫⁻ x : ℝ, if b < x then
          ENNReal.ofReal (Real.exp (-x^2/2)) *
            markedRealGaussianCharpolyMoment m x else 0) *
        (ENNReal.ofReal ((Real.sqrt (2*Real.pi))^(m+1)))⁻¹ := by
  let C : ℝ := (Real.sqrt (2*Real.pi))^
    ((Fintype.card (RealSchurMixedCoord (markedRealTwoBlockSizes m)))^2)
  have hC : 0 < C := by dsimp [C]; positivity
  let d : ℝ≥0∞ := ENNReal.ofReal ((Real.sqrt (2*Real.pi))^(m^2+m))
  have hscalar :
      (∫⁻ x : ℝ, if b < x then
        ENNReal.ofReal (Real.exp (-x^2/2)) * d *
          markedRealGaussianCharpolyMoment m x else 0) =
      (∫⁻ x : ℝ, if b < x then
        ENNReal.ofReal (Real.exp (-x^2/2)) *
          markedRealGaussianCharpolyMoment m x else 0) * d := by
    rw [← lintegral_mul_const' _ _ (show d ≠ ∞ by
      dsimp only [d]
      exact ENNReal.ofReal_ne_top)]
    apply lintegral_congr
    intro x
    by_cases hb : b < x
    · simp only [if_pos hb]
      ac_rfl
    · simp [hb]
  rw [realGaussian_markedRootCount_eq_mixedDensityIntegral]
  change (∫⁻ y, markedRealSimpleRootCount m b
    ((realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y) *
      ENNReal.ofReal (realSchurMixedGaussianCoordinateWeight
        (markedRealTwoBlockSizes m) y / C)
      ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m)) = _
  simp_rw [ENNReal.ofReal_div_of_pos hC, div_eq_mul_inv, ← mul_assoc]
  rw [lintegral_mul_const' _ _ (by simp [hC]),
    markedRealStereo_gaussian_rootCount_eq_moment m hm b]
  change (∫⁻ w, markedRealStereoAngularWeight m w) *
    (∫⁻ x : ℝ, if b < x then
      ENNReal.ofReal (Real.exp (-x^2/2)) * d *
        markedRealGaussianCharpolyMoment m x else 0) * (ENNReal.ofReal C)⁻¹ = _
  rw [hscalar]
  calc
    _ = (∫⁻ w, markedRealStereoAngularWeight m w) *
        (∫⁻ x : ℝ, if b < x then
          ENNReal.ofReal (Real.exp (-x^2/2)) *
            markedRealGaussianCharpolyMoment m x else 0) *
          (d * (ENNReal.ofReal C)⁻¹) := by ac_rfl
    _ = _ := by
      rw [show d * (ENNReal.ofReal C)⁻¹ =
        (ENNReal.ofReal ((Real.sqrt (2*Real.pi))^(m+1)))⁻¹ from
          markedRealAngular_gaussianNormalizer_ratio m]
      simp only [div_eq_mul_inv]

#print axioms realGaussian_markedRootCount_stereo_moment
end SpectralRadiusUpperTail
