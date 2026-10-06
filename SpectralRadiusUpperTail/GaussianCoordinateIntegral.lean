import SpectralRadiusUpperTail.GaussianArrayExplicitDensity
import SpectralRadiusUpperTail.GaussianEuclideanDensity

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal BigOperators

theorem gaussianCoordinateWeight_eq_prod (n : ℕ) (u : Fin n → ℝ) :
    Real.exp (-(∑ i, (u i)^2)) = ∏ i, Real.exp (-(u i)^2) := by
  rw [← Real.exp_sum, Finset.sum_neg_distrib]

theorem gaussianCoordinateWeight_integrable (n : ℕ) :
    Integrable (fun u : Fin n → ℝ => Real.exp (-(∑ i, (u i)^2))) := by
  simp_rw [gaussianCoordinateWeight_eq_prod]
  exact Integrable.fintype_prod (fun _ : Fin n => by
    simpa only [neg_mul, one_mul] using integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1))

theorem gaussianCoordinateWeight_integral (n : ℕ) :
    (∫ u : Fin n → ℝ, Real.exp (-(∑ i, (u i)^2))) = (Real.sqrt Real.pi)^n := by
  simp_rw [gaussianCoordinateWeight_eq_prod]
  rw [integral_fintype_prod_volume_eq_prod (fun _ : Fin n => fun r : ℝ => Real.exp (-r^2))]
  have hs : (∫ r : ℝ, Real.exp (-r^2)) = Real.sqrt Real.pi := by
    simpa only [neg_mul, one_mul, div_one] using integral_gaussian (1 : ℝ)
  simp only [hs, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem gaussianCoordinateWeight_lintegral (n : ℕ) :
    (∫⁻ u : Fin n → ℝ, ENNReal.ofReal (Real.exp (-(∑ i, (u i)^2)))) =
      ENNReal.ofReal ((Real.sqrt Real.pi)^n) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (gaussianCoordinateWeight_integrable n)
    (Filter.Eventually.of_forall (fun _ => Real.exp_nonneg _)),
    gaussianCoordinateWeight_integral]

theorem euclideanGaussian_lintegral (n : ℕ) :
    (∫⁻ v : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (Real.exp (-‖v‖^2))) =
      ENNReal.ofReal ((Real.sqrt Real.pi)^n) := by
  have hf : Measurable (fun v : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (Real.exp (-‖v‖^2))) := by fun_prop
  rw [← (PiLp.volume_preserving_toLp (Fin n)).lintegral_comp hf]
  simpa only [EuclideanSpace.real_norm_sq_eq] using
    gaussianCoordinateWeight_lintegral n

theorem gaussian_halfline_lintegral :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-r^2))) =
      ENNReal.ofReal (Real.sqrt Real.pi / 2) := by
  have hi : Integrable (fun r : ℝ => Real.exp (-r^2)) := by
    simpa only [neg_mul, one_mul] using integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
  rw [← ofReal_integral_eq_lintegral_ofReal hi.integrableOn
    (Filter.Eventually.of_forall (fun _ => Real.exp_nonneg _))]
  congr 1
  simpa only [neg_mul, one_mul, div_one] using integral_gaussian_Ioi (1 : ℝ)

#print axioms gaussianCoordinateWeight_eq_prod
#print axioms gaussianCoordinateWeight_integrable
#print axioms gaussianCoordinateWeight_integral
#print axioms gaussianCoordinateWeight_lintegral
#print axioms euclideanGaussian_lintegral
#print axioms gaussian_halfline_lintegral
end SpectralRadiusUpperTail
