import SpectralRadiusUpperTail.RealSchurFixedFirstPatchTransport
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix ENNReal

/-- Exact nonoverlapping sum of local Schur Jacobian integrals over a
fixed countable atlas in the original matrix-entry coordinates. -/
theorem realSchurFixed_lintegral_atlas_patch_sum
    {n : ℕ} (c : ℕ → RealSchurFixedChartIndex n)
    (g : ((Fin n × Fin n) → ℝ) → ℝ≥0∞) :
    ∫⁻ x in ⋃ k, realSchurFixedEntryFirstPatch c k,
        g x ∂(volume : Measure ((Fin n × Fin n) → ℝ)) =
      ∑' k, ∫⁻ t in realSchurFixedChartPatchSource (c k)
          (realSchurFixedMixedFirstPatch c k),
        ENNReal.ofReal (realSchurMixedJacobianWeight
          (realSchurListBlockSize (c k).shape) (c k).frame.T t) *
          g ((realSchurFixedToMixedLinearEquiv (c k).indexEquiv).symm
            (realSchurMixedRotatedEntryCoordinates
              (realSchurListBlockSize (c k).shape) (c k).frame.T
              (c k).frame.Q (c k).frame.orthogonal t))
        ∂realSchurMixedCoordinateVolume
          (realSchurListBlockSize (c k).shape) := by
  rw [lintegral_iUnion (measurableSet_realSchurFixedEntryFirstPatch c)
    (pairwise_realSchurFixedEntryFirstPatch c) g]
  congr 1
  funext k
  exact realSchurFixed_lintegral_first_patch c k g

/-- Choose one countable fixed-coordinate atlas on the full regular
locus, independently of the integrand. -/
theorem exists_realSchurFixed_lintegral_regular_locus (n : ℕ) :
    ∃ c : ℕ → RealSchurFixedChartIndex n,
      ∀ (g : ((Fin n × Fin n) → ℝ) → ℝ≥0∞),
        (∫⁻ x in {x | Matrix.of x.curry ∈ realSchurFixedRegularLocus n},
          g x ∂(volume : Measure ((Fin n × Fin n) → ℝ))) =
          ∑' k, ∫⁻ t in realSchurFixedChartPatchSource (c k)
              (realSchurFixedMixedFirstPatch c k),
            ENNReal.ofReal (realSchurMixedJacobianWeight
              (realSchurListBlockSize (c k).shape) (c k).frame.T t) *
              g ((realSchurFixedToMixedLinearEquiv (c k).indexEquiv).symm
                (realSchurMixedRotatedEntryCoordinates
                  (realSchurListBlockSize (c k).shape) (c k).frame.T
                  (c k).frame.Q (c k).frame.orthogonal t))
            ∂realSchurMixedCoordinateVolume
              (realSchurListBlockSize (c k).shape) := by
  obtain ⟨c,hc⟩ := exists_realSchurFixedRegularAtlasSequence n
  refine ⟨c, ?_⟩
  intro g
  have hcover := iUnion_realSchurFixedEntryFirstPatch c
  rw [hc] at hcover
  change (∫⁻ x in (fun x => Matrix.of x.curry) ⁻¹'
    realSchurFixedRegularLocus n,
      g x ∂(volume : Measure ((Fin n × Fin n) → ℝ))) = _
  rw [← hcover]
  exact realSchurFixed_lintegral_atlas_patch_sum c g

#print axioms realSchurFixed_lintegral_atlas_patch_sum
#print axioms exists_realSchurFixed_lintegral_regular_locus
end SpectralRadiusUpperTail
