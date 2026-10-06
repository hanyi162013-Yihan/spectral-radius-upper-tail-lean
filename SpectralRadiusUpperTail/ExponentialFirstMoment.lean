import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped ENNReal

lemma expMeasure_eq_density (r : ℝ) : expMeasure r = volume.withDensity (exponentialPDF r) := rfl

lemma exponential_firstMoment_density (r : ℝ) (hr : 0 < r) (x : ℝ) :
    exponentialPDF r x * ENNReal.ofReal x =
      ENNReal.ofReal r⁻¹ * gammaPDF 2 r x := by
  by_cases hx : 0 ≤ x
  · rw [exponentialPDF_of_nonneg hx]
    unfold gammaPDF gammaPDFReal
    rw [if_pos hx]
    norm_num only [Real.rpow_two,Real.Gamma_two,div_one,show (2 : ℝ)-1 = 1 by norm_num,Real.rpow_one]
    rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
    <;> ring
  · rw [exponentialPDF_of_neg (lt_of_not_ge hx),gammaPDF_of_neg (lt_of_not_ge hx)]
    simp

lemma exponential_firstMoment_lintegral (r : ℝ) (hr : 0 < r) :
    (∫⁻ x : ℝ, ENNReal.ofReal x ∂expMeasure r) = ENNReal.ofReal r⁻¹ := by
  have hd : Measurable (exponentialPDF r) := (measurable_exponentialPDFReal r).ennreal_ofReal
  rw [expMeasure_eq_density,lintegral_withDensity_eq_lintegral_mul volume hd (by fun_prop)]
  simp only [Pi.mul_apply]
  simp_rw [exponential_firstMoment_density r hr]
  have hg : Measurable (gammaPDF 2 r) := (measurable_gammaPDFReal 2 r).ennreal_ofReal
  rw [lintegral_const_mul _ hg,lintegral_gammaPDF_eq_one (by norm_num : (0 : ℝ) < 2) hr,mul_one]

lemma exponential_nonnegative_ae (r : ℝ) (hr : 0 < r) : ∀ᵐ x : ℝ ∂expMeasure r, 0 ≤ x := by
  rw [ae_iff]
  simp only [not_le]
  change expMeasure r (Set.Iio 0) = 0
  rw [expMeasure_eq_density,withDensity_apply _ measurableSet_Iio]
  exact lintegral_exponentialPDF_of_nonpos le_rfl

#print axioms expMeasure_eq_density
#print axioms exponential_firstMoment_density
#print axioms exponential_firstMoment_lintegral
#print axioms exponential_nonnegative_ae
end SpectralRadiusUpperTail
