import SpectralRadiusUpperTail.ComplexGaussianMoments
import SpectralRadiusUpperTail.RCLikeCovariance
import SpectralRadiusUpperTail.RowNormalizerBound

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexConjugate ENNReal

/-- The projection covariance of one weighted proper entry requires no
independence between its real and imaginary parts. -/
lemma proper_complex_weighted_projection (μ : Measure ℂ)
    (hX : MemLp (fun x : ℂ => x) 2 μ)
    (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1) (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (s v : ℂ) :
    (∫ x : ℂ, (inner ℝ s (v*x))^2 ∂μ) = ‖s‖^2*‖v‖^2/2 := by
  have hi (x : ℂ) : inner ℝ s (v*x) = RCLike.re ((conj s*v)*x) := by
    rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply', mul_assoc]
  simp_rw [hi]
  rw [rclike_projection_secondMoment μ hX, hvar, hpseudo]
  simp [norm_mul, mul_pow]

/-- Actual iid row sums have the full proper covariance quadratic form. -/
theorem proper_complex_row_projection_secondMoment (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : ℂ => x) 2 μ) (hm : (∫ x : ℂ, x ∂μ) = 0)
    (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1) (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (N : ℕ) (v : Fin N → ℂ) (s : ℂ) :
    (∫ x : Fin N → ℂ, (inner ℝ s (∑ i, v i*x i))^2 ∂Measure.pi (fun _ => μ)) =
      ‖s‖^2*(∑ i, ‖v i‖^2)/2 := by
  have hF (i : Fin N) : MemLp (fun x : ℂ => inner ℝ s (v i*x)) 2 μ :=
    (hX.const_mul (v i)).const_inner s
  have hmF (i : Fin N) : (∫ x : ℂ, inner ℝ s (v i*x) ∂μ) = 0 := by
    rw [integral_inner ((hX.const_mul (v i)).integrable (by norm_num)),
      integral_const_mul, hm, mul_zero, inner_zero_right]
  have hh := product_sum_norm_sq μ (fun i x => inner ℝ s (v i*x)) hF hmF
  simp only [Real.norm_eq_abs, sq_abs] at hh
  simp_rw [inner_sum]
  rw [hh]
  simp_rw [proper_complex_weighted_projection μ hX hvar hpseudo]
  rw [← Finset.sum_div, ← Finset.mul_sum]

lemma proper_complex_row_projection_mean (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : ℂ => x) 2 μ) (hm : (∫ x : ℂ, x ∂μ) = 0)
    (N : ℕ) (v : Fin N → ℂ) (s : ℂ) :
    (∫ x : Fin N → ℂ, inner ℝ s (∑ i, v i*x i) ∂Measure.pi (fun _ => μ)) = 0 := by
  rw [integral_inner ((iid_linear_row_memLp μ v hX).integrable (by norm_num)),
    iid_linear_row_mean μ v hX hm, inner_zero_right]

theorem proper_complex_row_projection_variance (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : ℂ => x) 2 μ) (hm : (∫ x : ℂ, x ∂μ) = 0)
    (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1) (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (N : ℕ) (v : Fin N → ℂ) (s : ℂ) :
    variance (fun x : Fin N → ℂ => inner ℝ s (∑ i, v i*x i))
      (Measure.pi (fun _ => μ)) = ‖s‖^2*(∑ i, ‖v i‖^2)/2 := by
  have hrow : MemLp (fun x : Fin N → ℂ => inner ℝ s (∑ i, v i*x i)) 2
      (Measure.pi (fun _ => μ)) := (iid_linear_row_memLp μ v hX).const_inner s
  rw [variance_eq_integral hrow.aestronglyMeasurable.aemeasurable,
    proper_complex_row_projection_mean μ hX hm]
  simp only [sub_zero]
  exact proper_complex_row_projection_secondMoment μ hX hm hvar hpseudo N v s

#print axioms proper_complex_row_projection_secondMoment
#print axioms proper_complex_row_projection_variance
end SpectralRadiusUpperTail
