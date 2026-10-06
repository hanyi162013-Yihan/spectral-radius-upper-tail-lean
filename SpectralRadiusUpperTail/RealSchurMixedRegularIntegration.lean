import SpectralRadiusUpperTail.RealSchurMixedRegularAtlas
import SpectralRadiusUpperTail.RealSchurMixedLocalIntegration
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator

/-- The fixed-entry version of a regular mixed-Schur chart is injective
on its inverse-function-theorem source. -/
theorem realSchurMixedRegularEntryCoordinates_injOn_source
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hdet : (realSchurMixedOrbitMatrix s T).det ≠ 0) :
    Set.InjOn (realSchurMixedEntryCoordinates s T)
      (realSchurMixedRegularChart s T hdet).source := by
  intro x hx y hy he
  exact (realSchurMixedRegularChart s T hdet).injOn hx hy
    ((realSchurMixedEntryEquiv s).injective he)

/-- Exact local change of variables at any regular block-upper center.
The Jacobian uses the current diagonal blocks at every chart parameter. -/
theorem realSchurMixed_lintegral_regular_chart
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : realSchurMixedLowerProjection s T = 0)
    (hdet : (realSchurMixedOrbitMatrix s T).det ≠ 0)
    (U : Set (RealSchurMixedTangent s))
    (hU : MeasurableSet U)
    (hsub : U ⊆ (realSchurMixedRegularChart s T hdet).source)
    (g : RealSchurMixedTangent s → ℝ≥0∞) :
    ∫⁻ y in realSchurMixedEntryCoordinates s T '' U,
        g y ∂realSchurMixedCoordinateVolume s =
      ∫⁻ x in U,
        ENNReal.ofReal (realSchurMixedJacobianWeight s T x) *
          g (realSchurMixedEntryCoordinates s T x)
        ∂realSchurMixedCoordinateVolume s := by
  let : Measure.IsAddHaarMeasure (realSchurMixedCoordinateVolume s) :=
    realSchurMixedCoordinateVolume_isAddHaarMeasure s
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (realSchurMixedCoordinateVolume s) hU
    (fun x _ => (realSchurMixedEntryCoordinates_differentiable s T x).hasFDerivAt.hasFDerivWithinAt)
    ((realSchurMixedRegularEntryCoordinates_injOn_source s T hdet).mono hsub) g
  simpa only [realSchurMixedJacobianWeight_eq_abs_det s hs T hT] using h

#print axioms realSchurMixed_lintegral_regular_chart
end SpectralRadiusUpperTail
