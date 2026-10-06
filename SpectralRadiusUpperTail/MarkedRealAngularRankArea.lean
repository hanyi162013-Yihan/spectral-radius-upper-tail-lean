import SpectralRadiusUpperTail.MarkedRealRankFiberConst
import SpectralRadiusUpperTail.RealSchurMixedLocalIntegration
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator

/-- A rank layer admits a direct global area formula on every measurable
subset of its angular/upper product. The rank prevents collisions from
different real eigenvalues; no center-dependent patch restriction occurs. -/
theorem markedRealAngularRank_lintegral_image
    (m k : ℕ) (hm : 0 < m) (b : ℝ)
    (U : Set (RealSchurMixedTangent (markedRealTwoBlockSizes m)))
    (hU : MeasurableSet U)
    (hsub : U ⊆
      markedRealAngularPositiveSource m ×ˢ
        markedRealUpperRankSource m k b)
    (g : RealSchurMixedTangent (markedRealTwoBlockSizes m) → ℝ≥0∞) :
    (∫⁻ y in
      realSchurMixedEntryCoordinates (markedRealTwoBlockSizes m) 0 '' U,
      g y ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m)) =
    ∫⁻ x in U,
      ENNReal.ofReal (
        |(markedRealComplement m x.2.val -
            markedRealScalar m x.2.val •
              (1 : Matrix (Fin m) (Fin m) ℝ)).det| *
          |realSchurMixedAngularJacobian
            (markedRealTwoBlockSizes m) x.1|) *
        g (realSchurMixedEntryCoordinates
          (markedRealTwoBlockSizes m) 0 x)
        ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m) := by
  let s := markedRealTwoBlockSizes m
  let : Measure.IsAddHaarMeasure (realSchurMixedCoordinateVolume s) :=
    realSchurMixedCoordinateVolume_isAddHaarMeasure s
  have hinj : Set.InjOn (realSchurMixedEntryCoordinates s 0) U := by
    intro x hx y hy heq
    apply markedRealAngular_matrixMap_injOn_rank m k hm b
      (hsub hx) (hsub hy)
    have hmat := (realSchurMixedEntryEquiv s).injective heq
    simpa only [markedRealAngularProductMap,
      realSchurMixedEntryCoordinates,
      realSchurMixedExpCoordinates_eq_conjugation,
      zero_add] using hmat
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (realSchurMixedCoordinateVolume s) hU
    (fun x _ => (realSchurMixedEntryCoordinates_differentiable s 0 x).hasFDerivAt.hasFDerivWithinAt)
    hinj g
  have hs : ∀ i, 0 < s i := by
    intro i
    fin_cases i <;> simp [s, markedRealTwoBlockSizes, hm]
  have hweight (x : RealSchurMixedTangent s) :
      |(fderiv ℝ (realSchurMixedEntryCoordinates s 0) x).det| =
        |(markedRealComplement m x.2.val -
            markedRealScalar m x.2.val •
              (1 : Matrix (Fin m) (Fin m) ℝ)).det| *
          |realSchurMixedAngularJacobian s x.1| := by
    rw [← realSchurMixedJacobianWeight_eq_abs_det s hs 0
      (by simp : realSchurMixedLowerProjection s 0 = 0)]
    simpa only [zero_add] using
      markedRealTwoBlock_jacobianWeight m hm 0
        (by simp : realSchurMixedLowerProjection s 0 = 0) x
  simpa only [hweight] using h

#print axioms markedRealAngularRank_lintegral_image
end SpectralRadiusUpperTail
