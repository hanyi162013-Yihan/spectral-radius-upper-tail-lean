import SpectralRadiusUpperTail.ScaledSimplexHalfMass
import SpectralRadiusUpperTail.ExponentialProductDensity

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

lemma exponential_scaled_simplex_half (m : ℕ) (N : ℝ) (hN : 0 < N) (hm : (m : ℝ) ≤ N)
    (r : Fin m → ℝ) (hr : ∀ i, 1 ≤ r i) :
    (1/2 : ℝ≥0∞) ≤ (Measure.pi (fun i => expMeasure (r i))) (positiveSimplexAt m (2*N)) := by
  have hp (i : Fin m) : 0 < r i := lt_of_lt_of_le (by norm_num) (hr i)
  letI (i : Fin m) : IsProbabilityMeasure (expMeasure (r i)) := isProbabilityMeasure_expMeasure (hp i)
  apply scaled_simplex_mass_ge_half m (2*N) (by positivity)
  · apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval (fun j => expMeasure (r j)) i).quasiMeasurePreserving.ae
      (exponential_nonnegative_ae (r i) (hp i))
  · rw [lintegral_finsetSum _ (fun i _ => by fun_prop)]
    simp_rw [(measurePreserving_eval (fun j => expMeasure (r j)) _).lintegral_comp
      (show Measurable (fun x : ℝ => ENNReal.ofReal x) by fun_prop)]
    simp only [exponential_firstMoment_lintegral _ (hp _)]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => inv_nonneg.mpr (hp i).le)]
    apply ENNReal.ofReal_le_ofReal
    have hh : ∑ i, (r i)⁻¹ ≤ (m : ℝ) := by
      simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => inv_le_one_of_one_le₀ (hr i))
    linarith

lemma exponential_scaled_simplex_mass_identity (m : ℕ) (T : ℝ) (r : Fin m → ℝ) (hr : ∀ i, 0 < r i) :
    (Measure.pi (fun i => expMeasure (r i))) (positiveSimplexAt m T) =
      ENNReal.ofReal (∏ i, r i) *
        ∫⁻ x in positiveSimplexAt m T, ENNReal.ofReal (Real.exp (-(∑ i, r i*x i))) := by
  rw [exponential_product_density m r hr,withDensity_apply _ (positiveSimplexAt_measurable m T)]
  have he : (∫⁻ x in positiveSimplexAt m T, ENNReal.ofReal (∏ i, exponentialPDFReal (r i) (x i))) =
      ∫⁻ x in positiveSimplexAt m T, ENNReal.ofReal (∏ i, r i) *
        ENNReal.ofReal (Real.exp (-(∑ i, r i*x i))) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (positiveSimplexAt_measurable m T)] with x hx
    rw [exponential_product_density_nonneg m r x hx.1,
      ENNReal.ofReal_mul (Finset.prod_nonneg (fun i _ => (hr i).le))]
  rw [he,lintegral_const_mul _ (by fun_prop)]

lemma scaled_simplex_exponential_lintegral_lower (m : ℕ) (N : ℝ)
    (hN : 0 < N) (hm : (m : ℝ) ≤ N) (r : Fin m → ℝ) (hr : ∀ i, 1 ≤ r i) :
    (1/2 : ℝ≥0∞)*ENNReal.ofReal (∏ i, (r i)⁻¹) ≤
      ∫⁻ x in positiveSimplexAt m (2*N), ENNReal.ofReal (Real.exp (-(∑ i, r i*x i))) := by
  have hp : ∀ i, 0 < r i := fun i => lt_of_lt_of_le (by norm_num) (hr i)
  have hprod : 0 < ∏ i, r i := Finset.prod_pos (fun i _ => hp i)
  have hb := exponential_scaled_simplex_half m N hN hm r hr
  rw [exponential_scaled_simplex_mass_identity m (2*N) r hp] at hb
  have ht := mul_le_mul' (le_refl ((ENNReal.ofReal (∏ i, r i))⁻¹)) hb
  rw [← mul_assoc, ENNReal.inv_mul_cancel ((ENNReal.ofReal_pos.mpr hprod).ne')
    ENNReal.ofReal_ne_top, one_mul] at ht
  simpa only [Finset.prod_inv_distrib, ENNReal.ofReal_inv_of_pos hprod, mul_comm] using ht

#print axioms exponential_scaled_simplex_half
#print axioms exponential_scaled_simplex_mass_identity
#print axioms scaled_simplex_exponential_lintegral_lower
end SpectralRadiusUpperTail
