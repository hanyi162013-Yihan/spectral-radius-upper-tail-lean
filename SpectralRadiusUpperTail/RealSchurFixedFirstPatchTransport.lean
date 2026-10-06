import SpectralRadiusUpperTail.RealSchurFixedEntryFirstPatch
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix ENNReal

/-- The first-index patch of a fixed atlas, transported into the mixed
entry coordinates belonging to its own chart. -/
noncomputable def realSchurFixedMixedFirstPatch {n : ℕ}
    (c : ℕ → RealSchurFixedChartIndex n) (k : ℕ) :
    Set (RealSchurMixedTangent (realSchurListBlockSize (c k).shape)) :=
  realSchurFixedToMixedLinearEquiv (c k).indexEquiv ''
    realSchurFixedEntryFirstPatch c k

theorem measurableSet_realSchurFixedMixedFirstPatch {n : ℕ}
    (c : ℕ → RealSchurFixedChartIndex n) (k : ℕ) :
    MeasurableSet (realSchurFixedMixedFirstPatch c k) := by
  let E := realSchurFixedToMixedLinearEquiv (c k).indexEquiv
  have hEmb : MeasurableEmbedding E :=
    E.toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  exact hEmb.measurableSet_image'
    (measurableSet_realSchurFixedEntryFirstPatch c k)

theorem realSchurFixedMixedFirstPatch_subset_chart {n : ℕ}
    (c : ℕ → RealSchurFixedChartIndex n) (k : ℕ) :
    realSchurFixedMixedFirstPatch c k ⊆
      realSchurMixedEntryEquiv (realSchurListBlockSize (c k).shape) ''
        (c k).frame.chart.target := by
  rintro y ⟨x,hx,rfl⟩
  have htarget : x ∈ realSchurFixedChartEntryTarget (c k) := hx.1
  rw [realSchurFixedChartEntryTarget_eq_preimage] at htarget
  exact htarget

theorem realSchurFixedMixedFirstPatch_preimage {n : ℕ}
    (c : ℕ → RealSchurFixedChartIndex n) (k : ℕ) :
    (realSchurFixedToMixedLinearEquiv (c k).indexEquiv) ⁻¹'
      realSchurFixedMixedFirstPatch c k =
        realSchurFixedEntryFirstPatch c k := by
  let E := realSchurFixedToMixedLinearEquiv (c k).indexEquiv
  ext x
  constructor
  · rintro ⟨y,hy,heq⟩
    have hxy : y = x := E.injective heq
    simpa only [hxy] using hy
  · intro hx
    exact ⟨x,hx,rfl⟩

theorem realSchurFixed_lintegral_first_patch
    {n : ℕ} (c : ℕ → RealSchurFixedChartIndex n) (k : ℕ)
    (g : ((Fin n × Fin n) → ℝ) → ℝ≥0∞) :
    ∫⁻ x in realSchurFixedEntryFirstPatch c k,
        g x ∂(volume : Measure ((Fin n × Fin n) → ℝ)) =
      ∫⁻ t in realSchurFixedChartPatchSource (c k)
          (realSchurFixedMixedFirstPatch c k),
        ENNReal.ofReal (realSchurMixedJacobianWeight
          (realSchurListBlockSize (c k).shape) (c k).frame.T t) *
          g ((realSchurFixedToMixedLinearEquiv (c k).indexEquiv).symm
            (realSchurMixedRotatedEntryCoordinates
              (realSchurListBlockSize (c k).shape) (c k).frame.T
              (c k).frame.Q (c k).frame.orthogonal t))
        ∂realSchurMixedCoordinateVolume
          (realSchurListBlockSize (c k).shape) := by
  have h := realSchurFixed_lintegral_chart_patch
    (c k) (realSchurFixedMixedFirstPatch c k)
    (measurableSet_realSchurFixedMixedFirstPatch c k)
    (realSchurFixedMixedFirstPatch_subset_chart c k) g
  rwa [realSchurFixedMixedFirstPatch_preimage c k] at h

#print axioms realSchurFixed_lintegral_first_patch
end SpectralRadiusUpperTail
