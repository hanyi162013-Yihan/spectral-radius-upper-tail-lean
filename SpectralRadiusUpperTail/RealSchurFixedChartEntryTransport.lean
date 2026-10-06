import SpectralRadiusUpperTail.RealSchurFixedVolumeEquiv
import SpectralRadiusUpperTail.RealSchurMixedRegularPatchIntegration
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix ENNReal

/-- The target of a regular mixed-Schur chart expressed as original
`Fin n × Fin n` matrix entries. -/
def realSchurFixedChartEntryTarget {n : ℕ}
    (c : RealSchurFixedChartIndex n) :
    Set ((Fin n × Fin n) → ℝ) :=
  {x | Matrix.of x.curry ∈ c.target}

theorem realSchurFixedChartEntryTarget_eq_preimage {n : ℕ}
    (c : RealSchurFixedChartIndex n) :
    realSchurFixedChartEntryTarget c =
      (realSchurFixedToMixedLinearEquiv c.indexEquiv) ⁻¹'
        (realSchurMixedEntryEquiv (realSchurListBlockSize c.shape) ''
          c.frame.chart.target) := by
  ext x
  change Matrix.reindex c.indexEquiv c.indexEquiv
    (Matrix.of x.curry) ∈ c.frame.chart.target ↔ _
  rw [Set.mem_preimage, realSchurFixedToMixedLinearEquiv_apply,
    realSchurFixedToMixedTangent_eq_reindex]
  constructor
  · intro hx
    exact ⟨_, hx, rfl⟩
  · rintro ⟨A,hA,hEq⟩
    have hAeq :=
      (realSchurMixedEntryEquiv (realSchurListBlockSize c.shape)).injective hEq
    rwa [hAeq] at hA

theorem realSchurFixedChartEntryTarget_measurable {n : ℕ}
    (c : RealSchurFixedChartIndex n) :
    MeasurableSet (realSchurFixedChartEntryTarget c) := by
  rw [realSchurFixedChartEntryTarget_eq_preimage]
  have hEmb : MeasurableEmbedding
      (realSchurMixedEntryEquiv (realSchurListBlockSize c.shape)) :=
    (realSchurMixedEntryEquiv
      (realSchurListBlockSize c.shape)).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  exact (hEmb.measurableSet_image' c.frame.chart.open_target.measurableSet).preimage
    (realSchurFixedToMixedLinearEquiv c.indexEquiv).continuous_of_finiteDimensional.measurable

/-- The local rotated chart has exactly the advertised image in mixed
entry coordinates. -/
theorem realSchurFixedChart_rotatedEntry_image {n : ℕ}
    (c : RealSchurFixedChartIndex n) :
    realSchurMixedRotatedEntryCoordinates
      (realSchurListBlockSize c.shape) c.frame.T c.frame.Q
      c.frame.orthogonal '' c.frame.chart.source =
        realSchurMixedEntryEquiv (realSchurListBlockSize c.shape) ''
          c.frame.chart.target := by
  let s := realSchurListBlockSize c.shape
  let f := realSchurMixedRotatedEntryCoordinates s c.frame.T
    c.frame.Q c.frame.orthogonal
  have hf : f = (realSchurMixedEntryEquiv s) ∘ c.frame.chart := by
    funext x
    exact realSchurMixedRotatedEntryCoordinates_eq s c.frame.T
      c.frame.Q c.frame.orthogonal x |>.trans
        (congrArg (realSchurMixedEntryEquiv s)
          (realSchurMixedRegularRotatedChart_apply s c.frame.T
            c.frame.regular c.frame.Q c.frame.orthogonal x).symm)
  change f '' c.frame.chart.source = _
  rw [hf, Set.image_comp, c.frame.chart.image_source_eq_target]

#print axioms realSchurFixedChartEntryTarget_eq_preimage
#print axioms realSchurFixedChart_rotatedEntry_image
end SpectralRadiusUpperTail
