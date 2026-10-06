import SpectralRadiusUpperTail.MarkedRealChartSource
import SpectralRadiusUpperTail.MarkedRealTwoBlockGaussianChart
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set
open scoped ENNReal Matrix Matrix.Norms.Operator

/-- The same patch expressed in the entry-coordinate volume used by
the local area formula. -/
def markedRealChartEntryImage
    (m : ℕ) (b : ℝ)
    (c : ℕ → RealSchurMixedRegularFrame (markedRealTwoBlockSizes m))
    (k : ℕ) : Set (RealSchurMixedTangent (markedRealTwoBlockSizes m)) :=
  realSchurMixedEntryEquiv (markedRealTwoBlockSizes m) ''
    ((c k).chart '' markedRealChartFirstSource m b c k)

theorem markedRealChartEntryImage_eq_rotatedImage
    (m : ℕ) (b : ℝ)
    (c : ℕ → RealSchurMixedRegularFrame (markedRealTwoBlockSizes m))
    (k : ℕ) :
    markedRealChartEntryImage m b c k =
      realSchurMixedRotatedEntryCoordinates
        (markedRealTwoBlockSizes m) (c k).T (c k).Q (c k).orthogonal ''
          markedRealChartFirstSource m b c k := by
  rw [markedRealChartEntryImage, ← Set.image_comp]
  congr 1
  funext t
  rw [realSchurMixedRotatedEntryCoordinates_eq]
  change (realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)) ((c k).chart t) = _
  rw [RealSchurMixedRegularFrame.chart,
    realSchurMixedRegularRotatedChart_apply]

/-- The entry images of marked source patches are Borel, even though
images belonging to different real roots may overlap. -/
theorem measurableSet_markedRealChartEntryImage
    (m : ℕ) (b : ℝ)
    (c : ℕ → RealSchurMixedRegularFrame (markedRealTwoBlockSizes m))
    (k : ℕ) :
    MeasurableSet (markedRealChartEntryImage m b c k) := by
  rw [markedRealChartEntryImage_eq_rotatedImage]
  let f := realSchurMixedRotatedEntryCoordinates
    (markedRealTwoBlockSizes m) (c k).T (c k).Q (c k).orthogonal
  have hs := measurableSet_markedRealChartFirstSource m b c k
  have hdiff : Differentiable ℝ f :=
    (realSchurMixedOutputCoordinateEquiv (markedRealTwoBlockSizes m)
      (c k).Q (c k).orthogonal).toContinuousLinearEquiv.differentiable.comp
        (realSchurMixedEntryCoordinates_differentiable
          (markedRealTwoBlockSizes m) (c k).T)
  have hf' : ∀ t, t ∈ markedRealChartFirstSource m b c k →
      HasFDerivWithinAt f (fderiv ℝ f t)
        (markedRealChartFirstSource m b c k) t := by
    intro t _
    exact (hdiff t).hasFDerivAt.hasFDerivWithinAt
  have hinj : InjOn f (markedRealChartFirstSource m b c k) := by
    intro t ht u hu htu
    have hmat : (c k).chart t = (c k).chart u := by
      dsimp [f] at htu
      rw [realSchurMixedRotatedEntryCoordinates_eq,
        realSchurMixedRotatedEntryCoordinates_eq] at htu
      have h := (realSchurMixedEntryEquiv
        (markedRealTwoBlockSizes m)).injective htu
      simpa only [RealSchurMixedRegularFrame.chart,
        realSchurMixedRegularRotatedChart_apply] using h
    exact (c k).chart.injOn
      (markedRealChartFirstSource_subset_source m b c k ht)
      (markedRealChartFirstSource_subset_source m b c k hu) hmat
  exact measurable_image_of_fderivWithin hs hf' hinj

/-- Exact Gaussian local area formula on one marked-root patch. Its
Jacobian contains the complementary characteristic determinant. -/
theorem markedRealChart_gaussian_lintegral_firstPatch
    (m : ℕ) (hm : 0 < m) (b : ℝ)
    (c : ℕ → RealSchurMixedRegularFrame (markedRealTwoBlockSizes m))
    (k : ℕ)
    (g : RealSchurMixedTangent (markedRealTwoBlockSizes m) → ℝ≥0∞) :
    ∫⁻ y in markedRealChartEntryImage m b c k,
      ENNReal.ofReal (realSchurMixedGaussianCoordinateWeight
        (markedRealTwoBlockSizes m) y) * g y
        ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m) =
      ∫⁻ t in markedRealChartFirstSource m b c k,
        ENNReal.ofReal (
          |(markedRealComplement m ((c k).T+t.2.val) -
              markedRealScalar m ((c k).T+t.2.val) •
                (1 : Matrix (Fin m) (Fin m) ℝ)).det| *
            |realSchurMixedAngularJacobian (markedRealTwoBlockSizes m) t.1|) *
        (ENNReal.ofReal (realMatrixGaussianWeight
          (RealSchurMixedCoord (markedRealTwoBlockSizes m))
            ((c k).T+t.2.val)) *
          g (realSchurMixedRotatedEntryCoordinates
            (markedRealTwoBlockSizes m) (c k).T (c k).Q
              (c k).orthogonal t))
        ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m) := by
  rw [markedRealChartEntryImage_eq_rotatedImage]
  exact markedRealTwoBlock_gaussian_lintegral_local m hm
    (c k).T (c k).Q (c k).upper (c k).regular (c k).orthogonal
    (markedRealChartFirstSource m b c k)
    (measurableSet_markedRealChartFirstSource m b c k)
    (markedRealChartFirstSource_subset_source m b c k) g

#print axioms measurableSet_markedRealChartEntryImage
#print axioms markedRealChartEntryImage_eq_rotatedImage
#print axioms markedRealChart_gaussian_lintegral_firstPatch
end SpectralRadiusUpperTail
