import SpectralRadiusUpperTail.ExponentialCoordinateSplit
import SpectralRadiusUpperTail.ScaledSimplexHalfMass

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

lemma exponential_half_rate_simplex (m : ℕ) (N : ℝ) (hN : 0 < N) (hm : (m : ℝ) ≤ N) :
    (1/2 : ℝ≥0∞) ≤ (Measure.pi (fun _ : Fin m => expMeasure (1/2)))
      (positiveSimplexAt m (4*N)) := by
  letI : IsProbabilityMeasure (expMeasure (1/2)) := isProbabilityMeasure_expMeasure (by norm_num)
  apply scaled_simplex_mass_ge_half m (4*N) (by positivity)
  · apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval (fun _ : Fin m => expMeasure (1/2)) i).quasiMeasurePreserving.ae
      (exponential_nonnegative_ae (1/2) (by norm_num))
  · rw [lintegral_finsetSum _ (fun i _ => by fun_prop)]
    simp_rw [(measurePreserving_eval (fun _ : Fin m => expMeasure (1/2)) _).lintegral_comp
      (show Measurable (fun x : ℝ => ENNReal.ofReal x) by fun_prop)]
    simp only [exponential_firstMoment_lintegral _ (by norm_num : (0 : ℝ) < 1/2)]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
    apply ENNReal.ofReal_le_ofReal
    simp only [one_div, inv_inv, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith

lemma positive_normalized_coordinate_bound {m : ℕ} (h₀ y₀ : ℝ) (h y : Fin m → ℝ)
    (hh₀ : 0 ≤ h₀) (hh : ∀ i, 0 ≤ h i) (hy : ∀ i, 0 ≤ y i)
    (hy₀ : 0 < y₀) (hs : ∑ i, y i ≤ y₀) :
    h₀/2 ≤ (h₀*y₀+∑ i, h i*y i)/(y₀+∑ i, y i) := by
  have hsum : 0 ≤ ∑ i, y i := Finset.sum_nonneg (fun i _ => hy i)
  have hw : 0 ≤ ∑ i, h i*y i := Finset.sum_nonneg (fun i _ => mul_nonneg (hh i) (hy i))
  apply (le_div_iff₀ (by linarith : 0 < y₀+∑ i, y i)).mpr
  nlinarith [mul_nonneg hh₀ (sub_nonneg.mpr hs)]

lemma positive_exponential_first_coordinate {m : ℕ} (N a h₀ : ℝ) (h y : Fin m → ℝ)
    (hN : 0 < N) (ha : 0 ≤ a) (hh₀ : 0 ≤ h₀) (hh : ∀ i, 0 ≤ h i)
    (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i ≤ 4*N) :
    ENNReal.ofReal (Real.exp (a*h₀/2))*ENNReal.ofReal (Real.exp (-2*N)) ≤
      ∫⁻ y₀ : ℝ, exponentialWitnessIntegrand (-a) 1 h₀ h y₀ y ∂expMeasure (1/2) := by
  let C := ENNReal.ofReal (Real.exp (a*h₀/2))
  have hm : (∫⁻ _y₀ in Ioi (4*N), C ∂expMeasure (1/2)) ≤
      ∫⁻ y₀ in Ioi (4*N), exponentialWitnessIntegrand (-a) 1 h₀ h y₀ y ∂expMeasure (1/2) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y₀ hy₀
    change 4*N < y₀ at hy₀
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hb := mul_le_mul_of_nonneg_left
      (positive_normalized_coordinate_bound h₀ y₀ h y hh₀ hh hy (by linarith) (by linarith)) ha
    simpa only [neg_neg, div_one, mul_div_assoc] using hb
  rw [lintegral_const, Measure.restrict_apply_univ,
    exponential_tail (1/2) (4*N) (by norm_num) (by positivity)] at hm
  have he : -((1/2 : ℝ)*(4*N)) = -2*N := by ring
  rw [he] at hm
  exact hm.trans (setLIntegral_le_lintegral _ _)

#print axioms exponential_half_rate_simplex
#print axioms positive_normalized_coordinate_bound
#print axioms positive_exponential_first_coordinate
end SpectralRadiusUpperTail
