import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ComplexConjugate
variable {Ω 𝕂 : Type*} [MeasurableSpace Ω] [RCLike 𝕂]

lemma norm_sq_eq_re_mul_star (z : 𝕂) : ‖z‖^2 = RCLike.re (z * star z) := by
  change ‖z‖^2 = RCLike.re (z * conj z)
  rw [RCLike.mul_conj]
  simp only [← RCLike.ofReal_pow, RCLike.ofReal_re]

lemma norm_sq_integrable_of_mul_star {μ : Measure Ω} {f : Ω → 𝕂}
    (hf : Integrable (fun x => f x * star (f x)) μ) :
    Integrable (fun x => ‖f x‖^2) μ := by
  simp_rw [norm_sq_eq_re_mul_star]
  exact hf.re

lemma integral_norm_sq_le_norm_integral_mul_star {μ : Measure Ω} {f : Ω → 𝕂}
    (hf : Integrable (fun x => f x * star (f x)) μ) :
    (∫ x, ‖f x‖^2 ∂μ) ≤ ‖∫ x, f x * star (f x) ∂μ‖ := by
  simp_rw [norm_sq_eq_re_mul_star]
  rw [integral_re hf]
  exact RCLike.re_le_norm _

#print axioms norm_sq_eq_re_mul_star
#print axioms norm_sq_integrable_of_mul_star
#print axioms integral_norm_sq_le_norm_integral_mul_star
end SpectralRadiusUpperTail
