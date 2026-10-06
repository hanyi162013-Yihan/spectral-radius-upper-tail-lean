import SpectralRadiusUpperTail.RealSchurFixedChartEntryTransport
import SpectralRadiusUpperTail.RealSchurMixedRegularRotatedIntegration
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix ENNReal

/-- Change variables on one regular mixed-Schur chart, starting with
the original fixed matrix-entry Lebesgue measure. -/
theorem realSchurFixed_lintegral_chart
    {n : ℕ} (c : RealSchurFixedChartIndex n)
    (g : ((Fin n × Fin n) → ℝ) → ℝ≥0∞) :
    ∫⁻ x in realSchurFixedChartEntryTarget c,
        g x ∂(volume : Measure ((Fin n × Fin n) → ℝ)) =
      ∫⁻ t in c.frame.chart.source,
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
  let S := realSchurMixedEntryEquiv s '' c.frame.chart.target
  have hEmb : MeasurableEmbedding (realSchurMixedEntryEquiv s) :=
    (realSchurMixedEntryEquiv s).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  have hS : MeasurableSet S :=
    hEmb.measurableSet_image' c.frame.chart.open_target.measurableSet
  have htransport := realSchurFixedToMixedLinearEquiv_setLIntegral
    c.indexEquiv S hS (fun y => g (E.symm y))
  have htransport' :
      (∫⁻ x in realSchurFixedChartEntryTarget c,
        g x ∂(volume : Measure ((Fin n × Fin n) → ℝ))) =
      ∫⁻ y in S, g (E.symm y) ∂realSchurMixedCoordinateVolume s := by
    rw [realSchurFixedChartEntryTarget_eq_preimage]
    change (∫⁻ x in E ⁻¹' S,
      g x ∂(volume : Measure ((Fin n × Fin n) → ℝ))) = _
    change (∫⁻ x in E ⁻¹' S,
      g (E.symm (E x)) ∂(volume : Measure ((Fin n × Fin n) → ℝ))) = _ at htransport
    simpa only [LinearEquiv.symm_apply_apply] using htransport
  have hlocal := realSchurMixed_lintegral_regular_rotated_chart
    s c.positive c.frame.T c.frame.Q c.frame.upper c.frame.regular
    c.frame.orthogonal c.frame.chart.source
    c.frame.chart.open_source.measurableSet (by intro t ht; exact ht)
    (fun y => g (E.symm y))
  rw [realSchurFixedChart_rotatedEntry_image] at hlocal
  exact htransport'.trans hlocal

#print axioms realSchurFixed_lintegral_chart
end SpectralRadiusUpperTail
