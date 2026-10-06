import SpectralRadiusUpperTail.RealSchurFixedFullIntegration
import SpectralRadiusUpperTail.RealGaussianMatrixExplicitDensity
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix ENNReal

/-- The explicit density of the iid real Gaussian matrix on its original
fixed entry array. -/
noncomputable def realGaussianFixedDensity (n : ℕ)
    (x : (Fin n × Fin n) → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (realGaussianMatrixWeight n x /
    (Real.sqrt (2*Real.pi))^(n*n))

theorem measurable_realGaussianFixedDensity (n : ℕ) :
    Measurable (realGaussianFixedDensity n) := by
  unfold realGaussianFixedDensity realGaussianMatrixWeight
  fun_prop

theorem realGaussianFixedDensity_lt_top (n : ℕ)
    (x : (Fin n × Fin n) → ℝ) :
    realGaussianFixedDensity n x < ∞ := by
  simp [realGaussianFixedDensity]

/-- Exact global Gaussian integration over the fixed real-Schur atlas.
The formula retains the first-chart source restrictions and therefore
does not yet evaluate the eigenvalue one-point density. -/
theorem exists_realGaussianFixedSchurIntegration (n : ℕ) :
    ∃ c : ℕ → RealSchurFixedChartIndex n,
      ∀ (g : ((Fin n × Fin n) → ℝ) → ℝ≥0∞),
        (∫⁻ x, g x ∂gaussianMatrixLaw n) =
          ∑' k, ∫⁻ t in realSchurFixedChartPatchSource (c k)
              (realSchurFixedMixedFirstPatch c k),
            ENNReal.ofReal (realSchurMixedJacobianWeight
              (realSchurListBlockSize (c k).shape) (c k).frame.T t) *
              (realGaussianFixedDensity n
                ((realSchurFixedToMixedLinearEquiv (c k).indexEquiv).symm
                  (realSchurMixedRotatedEntryCoordinates
                    (realSchurListBlockSize (c k).shape) (c k).frame.T
                    (c k).frame.Q (c k).frame.orthogonal t)) *
                g ((realSchurFixedToMixedLinearEquiv (c k).indexEquiv).symm
                  (realSchurMixedRotatedEntryCoordinates
                    (realSchurListBlockSize (c k).shape) (c k).frame.T
                    (c k).frame.Q (c k).frame.orthogonal t)))
            ∂realSchurMixedCoordinateVolume
              (realSchurListBlockSize (c k).shape) := by
  obtain ⟨c,hc⟩ := exists_realSchurFixed_lintegral_full n
  refine ⟨c, ?_⟩
  intro g
  have hd := measurable_realGaussianFixedDensity n
  have hweight := hc
    (fun x => realGaussianFixedDensity n x * g x)
  have hmeasure : gaussianMatrixLaw n =
      (volume : Measure ((Fin n × Fin n) → ℝ)).withDensity
        (realGaussianFixedDensity n) :=
    gaussianMatrixLaw_eq_explicitDensity n
  rw [hmeasure,
    lintegral_withDensity_eq_lintegral_mul_non_measurable volume hd
      (Filter.Eventually.of_forall (realGaussianFixedDensity_lt_top n))]
  exact hweight

#print axioms exists_realGaussianFixedSchurIntegration
end SpectralRadiusUpperTail
