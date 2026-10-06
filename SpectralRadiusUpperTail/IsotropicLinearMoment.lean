import SpectralRadiusUpperTail.HilbertCovariance
import SpectralRadiusUpperTail.RCLikeCovariance
import Mathlib.Analysis.InnerProductSpace.Dual

namespace SpectralRadiusUpperTail
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma isotropic_projection_product (μ : Measure E)
    (hX : MemLp (fun x : E => x) 2 μ) (c : ℝ)
    (hc : ∀ s : E, (∫ x : E, (inner ℝ s x)^2 ∂μ) = c*‖s‖^2) (s w : E) :
    (∫ x : E, inner ℝ s x*inner ℝ w x ∂μ) = c*inner ℝ s w := by
  rw [hilbert_projection_product_integral μ hX, hc, hc, hc, norm_add_sq_real]
  ring

/-- Isotropic covariance cancels the linear term against every continuous
real linear functional, including functionals composed with complex multiplication. -/
theorem isotropic_linear_moment (μ : Measure E)
    (hX : MemLp (fun x : E => x) 2 μ) (c : ℝ)
    (hc : ∀ s : E, (∫ x : E, (inner ℝ s x)^2 ∂μ) = c*‖s‖^2)
    (L : E →L[ℝ] ℝ) (w : E) :
    Integrable (fun x : E => inner ℝ w x*L x) μ ∧
      (∫ x : E, inner ℝ w x*L x ∂μ) = c*L w := by
  let z := (InnerProductSpace.toDual ℝ E).symm L
  have hz (x : E) : inner ℝ z x = L x := InnerProductSpace.toDual_symm_apply
  constructor
  · simpa only [hz] using hilbert_projection_product_integrable μ hX w z
  · have hh := isotropic_projection_product μ hX c hc w z
    rw [real_inner_comm z w, hz] at hh
    simpa only [hz] using hh

lemma real_unit_covariance (μ : Measure ℝ)
    (hvar : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1) (s : ℝ) :
    (∫ x : ℝ, (inner ℝ s x)^2 ∂μ) = 1*‖s‖^2 := by
  have hi (x : ℝ) : inner ℝ s x = s*x := by
    rw [RCLike.inner_apply']
    rfl
  simp only [hi, mul_pow, integral_const_mul, Real.norm_eq_abs, sq_abs] at hvar ⊢
  rw [hvar]
  ring

lemma proper_unit_covariance (μ : Measure ℂ)
    (hX : MemLp (fun x : ℂ => x) 2 μ)
    (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1) (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (s : ℂ) : (∫ x : ℂ, (inner ℝ s x)^2 ∂μ) = (1/2)*‖s‖^2 := by
  rw [proper_complex_covariance μ hX hvar hpseudo]
  ring

#print axioms isotropic_linear_moment
#print axioms real_unit_covariance
#print axioms proper_unit_covariance
end SpectralRadiusUpperTail
