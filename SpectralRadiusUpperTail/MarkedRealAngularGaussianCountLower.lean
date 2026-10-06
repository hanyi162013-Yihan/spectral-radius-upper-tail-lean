import SpectralRadiusUpperTail.MarkedRealAngularGaussianMomentSimple
import SpectralRadiusUpperTail.MarkedRealAngularImageCountIntegral
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix

/-- The explicit single-angular-chart characteristic-polynomial integral
is a lower bound for the actual Gaussian-weighted real-root count. -/
theorem markedRealAngular_gaussianMoment_le_rootCountIntegral
    (m : ℕ) (hm : 0 < m) (b : ℝ) :
    (∫⁻ ω, markedRealAngularWeight m ω) *
        (∫⁻ x : ℝ,
          if b < x then
            ENNReal.ofReal (Real.exp (-x^2/2)) *
              ENNReal.ofReal ((Real.sqrt (2*Real.pi))^(m^2+m)) *
              markedRealGaussianCharpolyMoment m x
          else 0) ≤
      ∫⁻ y,
        markedRealSimpleRootCount m b
          ((realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y) *
        ENNReal.ofReal
          (realSchurMixedGaussianCoordinateWeight
            (markedRealTwoBlockSizes m) y)
          ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m) := by
  let s := markedRealTwoBlockSizes m
  have hw : Continuous (realMatrixGaussianWeight (RealSchurMixedCoord s)) := by
    unfold realMatrixGaussianWeight
    fun_prop
  have hgauss : Measurable (fun y : RealSchurMixedTangent s =>
      ENNReal.ofReal (realSchurMixedGaussianCoordinateWeight s y)) := by
    exact (hw.comp
      (realSchurMixedEntryEquiv s).symm.toContinuousLinearEquiv.continuous).measurable.ennreal_ofReal
  rw [← markedRealAngularRank_gaussian_area_tsum_moment_simple m hm b]
  exact markedRealAngularRank_lintegral_imageSum_le_rootCount
    m hm b _ hgauss

#print axioms markedRealAngular_gaussianMoment_le_rootCountIntegral
end SpectralRadiusUpperTail
