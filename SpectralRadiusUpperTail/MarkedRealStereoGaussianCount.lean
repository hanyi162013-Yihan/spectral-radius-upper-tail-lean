import SpectralRadiusUpperTail.MarkedRealStereoCountIntegral
import SpectralRadiusUpperTail.MarkedRealStereoGaussianMoment

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix

/-- The actual Gaussian-weighted real-root count equals an explicit
hemisphere mass times the complementary iid Gaussian determinant moment.
The hemisphere mass has not yet been replaced by its closed Gamma formula. -/
theorem markedRealStereo_gaussian_rootCount_eq_moment
    (m : ℕ) (hm : 0 < m) (b : ℝ) :
    (∫⁻ y, markedRealSimpleRootCount m b
        ((realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y) *
        ENNReal.ofReal (realSchurMixedGaussianCoordinateWeight (markedRealTwoBlockSizes m) y)
          ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m)) =
      (∫⁻ w, markedRealStereoAngularWeight m w) *
        (∫⁻ z : ℝ, if b < z then
          ENNReal.ofReal (Real.exp (-z^2/2)) *
            ENNReal.ofReal ((Real.sqrt (2*Real.pi))^(m^2+m)) *
              markedRealGaussianCharpolyMoment m z else 0) := by
  have hw : Continuous (realMatrixGaussianWeight
      (RealSchurMixedCoord (markedRealTwoBlockSizes m))) := by
    unfold realMatrixGaussianWeight
    fun_prop
  have hg : Measurable (fun y : RealSchurMixedTangent (markedRealTwoBlockSizes m) =>
      ENNReal.ofReal (realSchurMixedGaussianCoordinateWeight (markedRealTwoBlockSizes m) y)) :=
    (hw.comp (realSchurMixedEntryEquiv
      (markedRealTwoBlockSizes m)).symm.toContinuousLinearEquiv.continuous).measurable.ennreal_ofReal
  rw [← markedRealStereoRank_lintegral_imageSum_eq_rootCount m hm b _ hg]
  exact markedRealStereoRank_gaussian_area_tsum_moment_simple m hm b

#print axioms markedRealStereo_gaussian_rootCount_eq_moment
end SpectralRadiusUpperTail
