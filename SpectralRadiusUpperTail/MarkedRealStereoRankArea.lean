import SpectralRadiusUpperTail.MarkedRealStereoFullJacobian
import SpectralRadiusUpperTail.MarkedRealStereoInjective
import SpectralRadiusUpperTail.MarkedRealStereoSourceVolume
import SpectralRadiusUpperTail.MarkedRealUpperRankMeasurable

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator

theorem measurableSet_markedRealStereoRankProduct (m k : ℕ) (b : ℝ) :
    MeasurableSet (markedRealStereoSource m ×ˢ markedRealUpperRankSource m k b) := by
  exact prod_le_borel_prod _
    ((isOpen_markedRealStereoSource m).measurableSet.prod
      (measurableSet_markedRealUpperRankSource m k b))

/-- Direct global change of variables on a full hemisphere rank layer. -/
theorem markedRealStereoRank_lintegral_image (m k : ℕ) (hm : 0 < m) (b : ℝ)
    (g : RealSchurMixedTangent (markedRealTwoBlockSizes m) → ℝ≥0∞) :
    (∫⁻ y in markedRealStereoEntryMap m ''
      (markedRealStereoSource m ×ˢ markedRealUpperRankSource m k b),
      g y ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m)) =
      ∫⁻ x in (markedRealStereoSource m ×ˢ markedRealUpperRankSource m k b),
        ENNReal.ofReal
          (|(markedRealComplement m x.2.val - markedRealScalar m x.2.val •
              (1 : Matrix (Fin m) (Fin m) ℝ)).det| *
            |markedRealStereoAngularJacobian m x.1|) *
          g (markedRealStereoEntryMap m x)
            ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m) := by
  let s := markedRealTwoBlockSizes m
  let : Measure.IsAddHaarMeasure (realSchurMixedCoordinateVolume s) :=
    realSchurMixedCoordinateVolume_isAddHaarMeasure s
  have hh := lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (realSchurMixedCoordinateVolume s) (measurableSet_markedRealStereoRankProduct m k b)
    (fun x _ => (markedRealStereoEntryMap_differentiable m x).hasFDerivAt.hasFDerivWithinAt)
    (markedRealStereoEntryMap_injOn_rank m k hm b) g
  refine hh.trans ?_
  apply lintegral_congr
  intro x
  exact congrArg (fun t : ℝ => ENNReal.ofReal t * g (markedRealStereoEntryMap m x))
    (markedRealStereoEntryMap_fderiv_abs_det m x)

theorem markedRealStereoRank_gaussianArea (m k : ℕ) (hm : 0 < m) (b : ℝ) :
    (∫⁻ y in markedRealStereoEntryMap m ''
      (markedRealStereoSource m ×ˢ markedRealUpperRankSource m k b),
      ENNReal.ofReal (realSchurMixedGaussianCoordinateWeight (markedRealTwoBlockSizes m) y)
        ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m)) =
      ∫⁻ x in (markedRealStereoSource m ×ˢ markedRealUpperRankSource m k b),
        ENNReal.ofReal
          (|(markedRealComplement m x.2.val - markedRealScalar m x.2.val •
              (1 : Matrix (Fin m) (Fin m) ℝ)).det| *
            |markedRealStereoAngularJacobian m x.1|) *
          ENNReal.ofReal (realMatrixGaussianWeight
            (RealSchurMixedCoord (markedRealTwoBlockSizes m)) x.2.val)
            ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m) := by
  rw [markedRealStereoRank_lintegral_image m k hm b]
  simp only [markedRealStereoEntryMap_gaussianWeight]

#print axioms measurableSet_markedRealStereoRankProduct
#print axioms markedRealStereoRank_lintegral_image
#print axioms markedRealStereoRank_gaussianArea
end SpectralRadiusUpperTail
