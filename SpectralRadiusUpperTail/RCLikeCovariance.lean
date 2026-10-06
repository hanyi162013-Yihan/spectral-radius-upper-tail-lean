import SpectralRadiusUpperTail.Centering
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ComplexConjugate
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]

lemma rclike_re_square_identity (z : 𝕂) :
    (RCLike.re z)^2 = (‖z‖^2+RCLike.re (z^2))/2 := by
  rw [RCLike.norm_sq_eq_def]
  simp only [pow_two, RCLike.mul_re]
  ring

/-- The full directional second moment is determined by the ordinary second
moment and pseudovariance, without independence of real and imaginary parts. -/
theorem rclike_projection_secondMoment (μ : Measure 𝕂)
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (v : 𝕂) :
    (∫ x : 𝕂, (RCLike.re (v*x))^2 ∂μ) =
      (‖v‖^2*(∫ x : 𝕂, ‖x‖^2 ∂μ)+RCLike.re (v^2*(∫ x : 𝕂, x^2 ∂μ)))/2 := by
  have h2 := (memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).mp hX
  have hx2 : Integrable (fun x : 𝕂 => x^2) μ := by
    convert! hX.integrable_mul hX using 1
    ext x
    simp [pow_two]
  have he (x : 𝕂) : (RCLike.re (v*x))^2 =
      (‖v‖^2*‖x‖^2+RCLike.re (v^2*x^2))/2 := by
    simpa only [norm_mul, mul_pow] using rclike_re_square_identity (v*x)
  simp_rw [he]
  rw [integral_div, integral_add (h2.const_mul _) (hx2.const_mul _).re,
    integral_const_mul, integral_re (hx2.const_mul _), integral_const_mul]

/-- Matching ordinary second moments and pseudovariances matches the entire real
covariance quadratic form in both the real and complex scalar fields. -/
theorem rclike_covariance_matching (μ ν : Measure 𝕂)
    (hXμ : MemLp (fun x : 𝕂 => x) 2 μ) (hXν : MemLp (fun x : 𝕂 => x) 2 ν)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = ∫ x : 𝕂, ‖x‖^2 ∂ν)
    (hpseudo : (∫ x : 𝕂, x^2 ∂μ) = ∫ x : 𝕂, x^2 ∂ν) (s : 𝕂) :
    (∫ x : 𝕂, (inner ℝ s x)^2 ∂μ) = ∫ x : 𝕂, (inner ℝ s x)^2 ∂ν := by
  have hi (x : 𝕂) : inner ℝ s x = RCLike.re (conj s*x) := by
    rw [real_inner_eq_re_inner 𝕂, RCLike.inner_apply']
  simp_rw [hi]
  rw [rclike_projection_secondMoment μ hXμ, rclike_projection_secondMoment ν hXν,
    hvar, hpseudo]

/-- Properness and unit absolute variance give the real covariance I/2. -/
theorem proper_complex_covariance (μ : Measure ℂ)
    (hX : MemLp (fun x : ℂ => x) 2 μ)
    (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1) (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (s : ℂ) : (∫ x : ℂ, (inner ℝ s x)^2 ∂μ) = ‖s‖^2/2 := by
  have hi (x : ℂ) : inner ℝ s x = RCLike.re (conj s*x) := by
    rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply']
  simp_rw [hi]
  rw [rclike_projection_secondMoment μ hX, hvar, hpseudo]
  simp

#print axioms rclike_projection_secondMoment
#print axioms rclike_covariance_matching
#print axioms proper_complex_covariance
end SpectralRadiusUpperTail
