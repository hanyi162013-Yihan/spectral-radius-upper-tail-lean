import SpectralRadiusUpperTail.MarkedRealAngularRankMeasurable
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set
open scoped ENNReal Matrix Matrix.Norms.Operator

/-- The matrix image of each fixed angular/rank layer is Borel. -/
theorem measurableSet_markedRealAngularRankImage
    (m k : ℕ) (hm : 0 < m) (b : ℝ) :
    MeasurableSet
      (realSchurMixedEntryCoordinates (markedRealTwoBlockSizes m) 0 ''
        (markedRealAngularPositiveSource m ×ˢ
          markedRealUpperRankSource m k b)) := by
  let s := markedRealTwoBlockSizes m
  let U := markedRealAngularPositiveSource m ×ˢ
    markedRealUpperRankSource m k b
  let f := realSchurMixedEntryCoordinates s 0
  have hs : MeasurableSet U :=
    measurableSet_markedRealAngularRankProduct m k b
  have hdiff : Differentiable ℝ f :=
    realSchurMixedEntryCoordinates_differentiable s 0
  have hf' : ∀ t, t ∈ U →
      HasFDerivWithinAt f (fderiv ℝ f t) U t := by
    intro t _
    exact (hdiff t).hasFDerivAt.hasFDerivWithinAt
  have hinj : InjOn f U := by
    intro x hx y hy heq
    apply markedRealAngular_matrixMap_injOn_rank m k hm b hx hy
    have hmat := (realSchurMixedEntryEquiv s).injective heq
    simpa only [markedRealAngularProductMap,
      realSchurMixedEntryCoordinates,
      realSchurMixedExpCoordinates_eq_conjugation,
      zero_add] using hmat
  exact measurable_image_of_fderivWithin hs hf' hinj

#print axioms measurableSet_markedRealAngularRankImage
end SpectralRadiusUpperTail
