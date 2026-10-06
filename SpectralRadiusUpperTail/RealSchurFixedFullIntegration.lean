import SpectralRadiusUpperTail.RealSchurFixedAtlasIntegration
import SpectralRadiusUpperTail.RealGaussianSimpleSpectrum
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix ENNReal

/-- The fixed-coordinate regular mixed-Schur atlas covers Lebesgue
almost every real matrix-entry array. -/
theorem realSchurFixedRegularLocus_ae_volume (n : ℕ) :
    ∀ᵐ x : (Fin n × Fin n) → ℝ
      ∂(volume : Measure ((Fin n × Fin n) → ℝ)),
      Matrix.of x.curry ∈ realSchurFixedRegularLocus n := by
  filter_upwards [charpoly_separable_ae_volume n] with x hx
  obtain ⟨s,hs,e,hchart⟩ :=
    realMatrix_exists_reindexed_regular_chart_of_separable
      (Matrix.of x.curry) hx
  exact (realSchurFixedRegularLocus_mem_iff _).mpr
    ⟨s, hs, e, hchart⟩

/-- A single fixed countable real-Schur atlas gives an exact global
change-of-variables formula on matrix-entry Lebesgue space. This does
not evaluate the remaining block integrals. -/
theorem exists_realSchurFixed_lintegral_full (n : ℕ) :
    ∃ c : ℕ → RealSchurFixedChartIndex n,
      ∀ (g : ((Fin n × Fin n) → ℝ) → ℝ≥0∞),
        (∫⁻ x, g x ∂(volume : Measure ((Fin n × Fin n) → ℝ))) =
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
  obtain ⟨c,hc⟩ := exists_realSchurFixed_lintegral_regular_locus n
  refine ⟨c, ?_⟩
  intro g
  calc
    (∫⁻ x, g x ∂(volume : Measure ((Fin n × Fin n) → ℝ))) =
        ∫⁻ x in {x | Matrix.of x.curry ∈ realSchurFixedRegularLocus n},
          g x ∂(volume : Measure ((Fin n × Fin n) → ℝ)) := by
      have hres :
          (volume : Measure ((Fin n × Fin n) → ℝ)).restrict
            {x | Matrix.of x.curry ∈ realSchurFixedRegularLocus n} =
              volume :=
        Measure.restrict_eq_self_of_ae_mem
          (realSchurFixedRegularLocus_ae_volume n)
      change (∫⁻ x, g x ∂(volume : Measure ((Fin n × Fin n) → ℝ))) =
        ∫⁻ x, g x ∂((volume : Measure ((Fin n × Fin n) → ℝ)).restrict
          {x | Matrix.of x.curry ∈ realSchurFixedRegularLocus n})
      rw [hres]
    _ = _ := hc g

#print axioms realSchurFixedRegularLocus_ae_volume
#print axioms exists_realSchurFixed_lintegral_full
end SpectralRadiusUpperTail
