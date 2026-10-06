import SpectralRadiusUpperTail.RealSchurFixedChartIntegration
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix ENNReal

/-- The part of a local source chart mapping into a selected measurable
output patch in mixed entry coordinates. -/
def realSchurFixedChartPatchSource {n : ℕ}
    (c : RealSchurFixedChartIndex n)
    (S : Set (RealSchurMixedTangent (realSchurListBlockSize c.shape))) :
    Set (RealSchurMixedTangent (realSchurListBlockSize c.shape)) :=
  c.frame.chart.source ∩
    (realSchurMixedRotatedEntryCoordinates
      (realSchurListBlockSize c.shape) c.frame.T c.frame.Q
      c.frame.orthogonal) ⁻¹' S

theorem measurableSet_realSchurFixedChartPatchSource {n : ℕ}
    (c : RealSchurFixedChartIndex n)
    (S : Set (RealSchurMixedTangent (realSchurListBlockSize c.shape)))
    (hS : MeasurableSet S) :
    MeasurableSet (realSchurFixedChartPatchSource c S) := by
  let s := realSchurListBlockSize c.shape
  have hcont : Continuous
      (realSchurMixedRotatedEntryCoordinates s c.frame.T c.frame.Q
        c.frame.orthogonal) :=
    (realSchurMixedOutputCoordinateEquiv s c.frame.Q
      c.frame.orthogonal).toContinuousLinearEquiv.continuous.comp
        (realSchurMixedEntryCoordinates_differentiable s c.frame.T).continuous
  exact c.frame.chart.open_source.measurableSet.inter
    (hS.preimage hcont.measurable)

theorem realSchurFixedChartPatchSource_image {n : ℕ}
    (c : RealSchurFixedChartIndex n)
    (S : Set (RealSchurMixedTangent (realSchurListBlockSize c.shape)))
    (hsub : S ⊆ realSchurMixedEntryEquiv
      (realSchurListBlockSize c.shape) '' c.frame.chart.target) :
    realSchurMixedRotatedEntryCoordinates
      (realSchurListBlockSize c.shape) c.frame.T c.frame.Q
      c.frame.orthogonal '' realSchurFixedChartPatchSource c S = S := by
  let s := realSchurListBlockSize c.shape
  let f := realSchurMixedRotatedEntryCoordinates s c.frame.T c.frame.Q
    c.frame.orthogonal
  change f '' (c.frame.chart.source ∩ f ⁻¹' S) = S
  rw [Set.image_inter_preimage, realSchurFixedChart_rotatedEntry_image]
  exact Set.inter_eq_right.mpr hsub

/-- The exact fixed-coordinate Jacobian formula on any measurable part
of one regular chart target. -/
theorem realSchurFixed_lintegral_chart_patch
    {n : ℕ} (c : RealSchurFixedChartIndex n)
    (S : Set (RealSchurMixedTangent (realSchurListBlockSize c.shape)))
    (hS : MeasurableSet S)
    (hsub : S ⊆ realSchurMixedEntryEquiv
      (realSchurListBlockSize c.shape) '' c.frame.chart.target)
    (g : ((Fin n × Fin n) → ℝ) → ℝ≥0∞) :
    ∫⁻ x in (realSchurFixedToMixedLinearEquiv c.indexEquiv) ⁻¹' S,
        g x ∂(volume : Measure ((Fin n × Fin n) → ℝ)) =
      ∫⁻ t in realSchurFixedChartPatchSource c S,
        ENNReal.ofReal (realSchurMixedJacobianWeight
          (realSchurListBlockSize c.shape) c.frame.T t) *
          g ((realSchurFixedToMixedLinearEquiv c.indexEquiv).symm
            (realSchurMixedRotatedEntryCoordinates
              (realSchurListBlockSize c.shape) c.frame.T c.frame.Q
              c.frame.orthogonal t))
        ∂realSchurMixedCoordinateVolume
          (realSchurListBlockSize c.shape) := by
  let s := realSchurListBlockSize c.shape
  let E := realSchurFixedToMixedLinearEquiv c.indexEquiv
  let f := realSchurMixedRotatedEntryCoordinates s c.frame.T c.frame.Q
    c.frame.orthogonal
  let U := realSchurFixedChartPatchSource c S
  have htransport := realSchurFixedToMixedLinearEquiv_setLIntegral
    c.indexEquiv S hS (fun y => g (E.symm y))
  have htransport' :
      (∫⁻ x in E ⁻¹' S,
        g x ∂(volume : Measure ((Fin n × Fin n) → ℝ))) =
      ∫⁻ y in S, g (E.symm y) ∂realSchurMixedCoordinateVolume s := by
    change (∫⁻ x in E ⁻¹' S,
      g (E.symm (E x)) ∂(volume : Measure ((Fin n × Fin n) → ℝ))) = _ at htransport
    simpa only [LinearEquiv.symm_apply_apply] using htransport
  have hlocal := realSchurMixed_lintegral_regular_rotated_chart
    s c.positive c.frame.T c.frame.Q c.frame.upper c.frame.regular
    c.frame.orthogonal U
    (measurableSet_realSchurFixedChartPatchSource c S hS)
    (by intro t ht; exact ht.1)
    (fun y => g (E.symm y))
  rw [realSchurFixedChartPatchSource_image c S hsub] at hlocal
  exact htransport'.trans hlocal

#print axioms realSchurFixed_lintegral_chart_patch
end SpectralRadiusUpperTail
