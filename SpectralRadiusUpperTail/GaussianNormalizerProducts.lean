import SpectralRadiusUpperTail.ComplexGaussianFiniteScore
import SpectralRadiusUpperTail.RealGaussianFiniteScore
import SpectralRadiusUpperTail.SpectralTiltTargetEnergy

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma complex_gaussian_normalizer_product_log {n : ℕ} (a : ℝ) (ha : 0 < a)
    (v : Fin n → ℂ) (hv : (∑ i, ‖v i‖^2) = 1) (t : Fin n → ℂ) :
    Real.log (∏ i, gaussianFiniteNormalizer properComplexGaussian a v (t i)) =
      (n : ℝ)*Real.log (a/(a+1))-(∑ i, ‖t i‖^2)/(a+1) := by
  have hden : 0 < a+1 := by linarith
  have hc : a/(a+1) ≠ 0 := ne_of_gt (div_pos ha hden)
  have hpos : ∀ i, gaussianFiniteNormalizer properComplexGaussian a v (t i) ≠ 0 := by
    intro i
    rw [properComplexGaussian_finite_normalizer a ha,hv]
    exact mul_ne_zero hc (Real.exp_ne_zero _)
  rw [Real.log_prod (fun i _ => hpos i)]
  simp_rw [properComplexGaussian_finite_normalizer a ha,hv,
    Real.log_mul hc (Real.exp_ne_zero _),Real.log_exp]
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,Finset.sum_div,Finset.sum_neg_distrib,neg_div,sub_eq_add_neg]

lemma real_gaussian_normalizer_product_log {n : ℕ} (a : ℝ) (ha : 0 < a)
    (v : Fin n → ℝ) (hv : (∑ i, ‖v i‖^2) = 1) (t : Fin n → ℝ) :
    Real.log (∏ i, gaussianFiniteNormalizer standardNormal a v (t i)) =
      (n : ℝ)*Real.log (Real.sqrt (a/(a+2)))-(∑ i, (t i)^2)/(a+2) := by
  have hden : 0 < a+2 := by linarith
  have hc : Real.sqrt (a/(a+2)) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (div_pos ha hden))
  have hpos : ∀ i, gaussianFiniteNormalizer standardNormal a v (t i) ≠ 0 := by
    intro i
    rw [realGaussian_finite_normalizer a ha,hv,mul_one]
    exact mul_ne_zero hc (Real.exp_ne_zero _)
  rw [Real.log_prod (fun i _ => hpos i)]
  simp_rw [realGaussian_finite_normalizer a ha,hv,mul_one,
    Real.log_mul hc (Real.exp_ne_zero _),Real.log_exp]
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,Finset.sum_div,Finset.sum_neg_distrib,neg_div,sub_eq_add_neg]

#print axioms complex_gaussian_normalizer_product_log
#print axioms real_gaussian_normalizer_product_log
end SpectralRadiusUpperTail
