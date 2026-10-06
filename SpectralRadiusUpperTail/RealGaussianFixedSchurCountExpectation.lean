import SpectralRadiusUpperTail.RealGaussianFixedSchurCountBridge
import SpectralRadiusUpperTail.RealGaussianExteriorCountsAE
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

theorem realGaussianExteriorCount_lintegral_eq_ofReal_expectation
    (n : ℕ) (hn : 0 < n) (r : ℝ) (i : Fin 3) :
    (∫⁻ x, ENNReal.ofReal (realGaussianExteriorCount n r i x)
      ∂gaussianMatrixLaw n) =
      ENNReal.ofReal (∫ x, realGaussianExteriorCount n r i x
        ∂gaussianMatrixLaw n) := by
  have hMeas := realGaussianExteriorCount_aemeasurable n hn r i
  have hInt : Integrable (realGaussianExteriorCount n r i)
      (gaussianMatrixLaw n) := by
    apply Integrable.of_bound hMeas.aestronglyMeasurable (n : ℝ)
    filter_upwards [] with x
    obtain ⟨h0,_,hTop⟩ := realGaussianExteriorCount_bounds n r i x
    simpa [Real.norm_eq_abs, abs_of_nonneg h0] using hTop
  have hNonneg : ∀ᵐ x ∂gaussianMatrixLaw n,
      0 ≤ realGaussianExteriorCount n r i x :=
    Filter.Eventually.of_forall (fun x =>
      (realGaussianExteriorCount_bounds n r i x).1)
  exact (ofReal_integral_eq_lintegral_ofReal hInt hNonneg).symm

/-- The two finite-dimensional expectation inputs can now be read as
explicit local Schur patch sums for the actual iid Gaussian matrix. -/
theorem exists_realGaussianExteriorCountSchurExpectation
    (n : ℕ) (hn : 0 < n) :
    ∃ c : ℕ → RealSchurFixedChartIndex n,
      ∀ (r : ℝ) (i : Fin 3),
        ENNReal.ofReal (∫ x, realGaussianExteriorCount n r i x
          ∂gaussianMatrixLaw n) =
          ∑' k, realGaussianFixedSchurPatchIntegral c k
            (fun x => ENNReal.ofReal (realGaussianExteriorCount n r i x)) := by
  obtain ⟨c,hc⟩ := exists_realGaussianExteriorCountSchurIntegral n
  refine ⟨c, ?_⟩
  intro r i
  exact (realGaussianExteriorCount_lintegral_eq_ofReal_expectation
    n hn r i).symm.trans (hc r i)

#print axioms exists_realGaussianExteriorCountSchurExpectation
end SpectralRadiusUpperTail
