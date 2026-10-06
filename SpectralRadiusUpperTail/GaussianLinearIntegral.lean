import SpectralRadiusUpperTail.GaussianNormIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

lemma gaussian_linear_lintegral (μ : Measure E) [μ.IsAddHaarMeasure]
    (A : E →ₗ[ℝ] E) (hA : LinearMap.det A ≠ 0) (c : ℝ) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (-c*‖A x‖^2)) ∂μ) =
      ENNReal.ofReal |(LinearMap.det A)⁻¹| *
        ∫⁻ x, ENNReal.ofReal (Real.exp (-c*‖x‖^2)) ∂μ := by
  have hm : Measurable (fun x : E => ENNReal.ofReal (Real.exp (-c*‖x‖^2))) := by fun_prop
  rw [← lintegral_map hm A.continuous_of_finiteDimensional.measurable,
    Measure.map_linearMap_addHaar_eq_smul_addHaar μ hA,lintegral_smul_measure,smul_eq_mul]

#print axioms gaussian_linear_lintegral
end SpectralRadiusUpperTail
