import SpectralRadiusUpperTail.RealGaussianFixedSchurIntegration
import SpectralRadiusUpperTail.RealGaussianRootCountInterface
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix ENNReal

/-- A single first-chart contribution to the real Gaussian integral,
with the original matrix statistic evaluated at the chart output. -/
noncomputable def realGaussianFixedSchurPatchIntegral
    {n : ℕ} (c : ℕ → RealSchurFixedChartIndex n) (k : ℕ)
    (g : ((Fin n × Fin n) → ℝ) → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ t in realSchurFixedChartPatchSource (c k)
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
      (realSchurListBlockSize (c k).shape)

/-- The same chosen atlas works for every nonnegative matrix statistic,
including the actual spectral-root counts. -/
theorem exists_realGaussianFixedSchurPatchIntegral (n : ℕ) :
    ∃ c : ℕ → RealSchurFixedChartIndex n,
      ∀ g : ((Fin n × Fin n) → ℝ) → ℝ≥0∞,
        (∫⁻ x, g x ∂gaussianMatrixLaw n) =
          ∑' k, realGaussianFixedSchurPatchIntegral c k g := by
  obtain ⟨c,hc⟩ := exists_realGaussianFixedSchurIntegration n
  refine ⟨c, ?_⟩
  intro g
  simpa only [realGaussianFixedSchurPatchIntegral] using hc g

/-- Every normalized exterior characteristic-root count has an exact
first-chart Schur integral representation. No one-point formula is used. -/
theorem exists_realGaussianExteriorCountSchurIntegral (n : ℕ) :
    ∃ c : ℕ → RealSchurFixedChartIndex n,
      ∀ (r : ℝ) (i : Fin 3),
        (∫⁻ x,
          ENNReal.ofReal (realGaussianExteriorCount n r i x)
            ∂gaussianMatrixLaw n) =
          ∑' k, realGaussianFixedSchurPatchIntegral c k
            (fun x => ENNReal.ofReal (realGaussianExteriorCount n r i x)) := by
  obtain ⟨c,hc⟩ := exists_realGaussianFixedSchurPatchIntegral n
  exact ⟨c, fun r i => hc _⟩

#print axioms exists_realGaussianExteriorCountSchurIntegral
end SpectralRadiusUpperTail
