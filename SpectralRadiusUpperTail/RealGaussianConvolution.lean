import SpectralRadiusUpperTail.RealGaussianReplacement
import Mathlib.Probability.Distributions.Gaussian.Real

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Completing the square for the actual Gaussian density times the soft weight. -/
lemma realGaussian_soft_density (q : ℝ≥0) (hq : q ≠ 0) (a : ℝ) (ha : 0 < a) (s x : ℝ) :
    gaussianPDFReal 0 q x*Real.exp (-(s-x)^2/a) =
      (Real.sqrt (a/(a+2*q))*Real.exp (-s^2/(a+2*q)))*
        gaussianPDFReal (2*q*s/(a+2*q)) (a*q/(a+2*q)).toNNReal x := by
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hq)
  have hd : 0 < a+2*q := by positivity
  have hpost : 0 < a*q/(a+2*q) := by positivity
  have hroot : Real.sqrt (2*Real.pi*(a*q/(a+2*q))) =
      Real.sqrt (a/(a+2*q))*Real.sqrt (2*Real.pi*q) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ a/(a+2*q))]
    congr 1
    field_simp <;> ring
  have hc : (Real.sqrt (2*Real.pi*q))⁻¹ =
      Real.sqrt (a/(a+2*q))*(Real.sqrt (2*Real.pi*(a*q/(a+2*q))))⁻¹ := by
    rw [hroot]
    have hcs : Real.sqrt (a/(a+2*q)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    field_simp
  have he : -x^2/(2*q)+(-(s-x)^2/a) =
      -s^2/(a+2*q)+(-(x-2*q*s/(a+2*q))^2/(2*(a*q/(a+2*q)))) := by
    field_simp <;> ring
  simp only [gaussianPDFReal, sub_zero, Real.coe_toNNReal _ hpost.le]
  rw [mul_assoc, ← Real.exp_add, he, Real.exp_add, hc]
  ring

/-- The actual real Gaussian-soft convolution, including the zero-variance law. -/
theorem realGaussian_soft_convolution (q : ℝ≥0) (a : ℝ) (ha : 0 < a) (s : ℝ) :
    (∫ x : ℝ, Real.exp (-(s-x)^2/a) ∂gaussianReal 0 q) =
      Real.sqrt (a/(a+2*q))*Real.exp (-s^2/(a+2*q)) := by
  by_cases hq : q = 0
  · simp [hq, ha.ne']
  · rw [integral_gaussianReal_eq_integral_smul hq]
    simp only [smul_eq_mul]
    simp_rw [realGaussian_soft_density q hq a ha s]
    rw [integral_const_mul, integral_gaussianPDFReal_eq_one]
    · ring
    · apply ne_of_gt
      have hqpos : 0 < (q : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hq)
      exact Real.toNNReal_pos.mpr (by positivity)

#print axioms realGaussian_soft_density
#print axioms realGaussian_soft_convolution
end SpectralRadiusUpperTail
