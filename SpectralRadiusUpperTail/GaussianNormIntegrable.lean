import SpectralRadiusUpperTail.PositiveWeightNormalizer
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

lemma gaussian_norm_integrable (μ : Measure E) [μ.IsAddHaarMeasure] (c : ℝ) (hc : 0 < c) :
    Integrable (fun x : E => Real.exp (-c*‖x‖^2)) μ := by
  apply (integrable_fun_norm_addHaar μ (f := fun r : ℝ => Real.exp (-c*r^2))).mpr
  have hi := integrableOn_rpow_mul_exp_neg_mul_sq hc
    (show (-1 : ℝ) < ((Module.finrank ℝ E-1 : ℕ) : ℝ) by
      have h := Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ E-1)
      linarith)
  simpa only [Real.rpow_natCast,smul_eq_mul] using hi

lemma gaussian_norm_normalizer_bounds (μ : Measure E) [μ.IsAddHaarMeasure] (c : ℝ) (hc : 0 < c) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (-c*‖x‖^2)) ∂μ) ≠ 0 ∧
    (∫⁻ x, ENNReal.ofReal (Real.exp (-c*‖x‖^2)) ∂μ) ≠ ∞ :=
  positiveWeight_lintegral_bounds μ _ (gaussian_norm_integrable μ c hc) (fun _ => Real.exp_pos _)

#print axioms gaussian_norm_integrable
#print axioms gaussian_norm_normalizer_bounds
end SpectralRadiusUpperTail
