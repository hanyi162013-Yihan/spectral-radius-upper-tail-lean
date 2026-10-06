import SpectralRadiusUpperTail.ExponentialProductDensity
import SpectralRadiusUpperTail.ExponentialSimplexMass

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

lemma exponential_simplex_mass_identity (m : ℕ) (r : Fin m → ℝ) (hr : ∀ i, 0 < r i) :
    (Measure.pi (fun i => expMeasure (r i))) (positiveSimplex m) =
      ENNReal.ofReal (∏ i, r i) *
        ∫⁻ x in positiveSimplex m, ENNReal.ofReal (Real.exp (-(∑ i, r i*x i))) := by
  rw [exponential_product_density m r hr,withDensity_apply _ (positiveSimplex_measurable m)]
  have he : (∫⁻ x in positiveSimplex m, ENNReal.ofReal (∏ i, exponentialPDFReal (r i) (x i))) =
      ∫⁻ x in positiveSimplex m, ENNReal.ofReal (∏ i, r i) *
        ENNReal.ofReal (Real.exp (-(∑ i, r i*x i))) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (positiveSimplex_measurable m)] with x hx
    rw [exponential_product_density_nonneg m r x hx.1,
      ENNReal.ofReal_mul (Finset.prod_nonneg (fun i _ => (hr i).le))]
  rw [he,lintegral_const_mul _ (by fun_prop)]

lemma simplex_exponential_lintegral_lower (m : ℕ) (r : Fin m → ℝ)
    (hr : ∀ i, 2*((m : ℝ)+1) ≤ r i) :
    (1/2 : ℝ≥0∞) * ENNReal.ofReal (∏ i, (r i)⁻¹) ≤
      ∫⁻ x in positiveSimplex m, ENNReal.ofReal (Real.exp (-(∑ i, r i*x i))) := by
  have hp : ∀ i, 0 < r i := fun i => lt_of_lt_of_le (by positivity) (hr i)
  have hprod : 0 < ∏ i, r i := Finset.prod_pos (fun i _ => hp i)
  have hb := exponential_product_simplex_half_of_rates m r hr
  rw [exponential_simplex_mass_identity m r hp] at hb
  have ht := mul_le_mul' (le_refl ((ENNReal.ofReal (∏ i, r i))⁻¹)) hb
  rw [← mul_assoc,ENNReal.inv_mul_cancel ((ENNReal.ofReal_pos.mpr hprod).ne')
    ENNReal.ofReal_ne_top,one_mul] at ht
  simpa only [Finset.prod_inv_distrib,ENNReal.ofReal_inv_of_pos hprod,mul_comm] using ht

#print axioms exponential_simplex_mass_identity
#print axioms simplex_exponential_lintegral_lower
end SpectralRadiusUpperTail
