import SpectralRadiusUpperTail.RealGaussianConvolution
import SpectralRadiusUpperTail.GaussianFiniteSumLaw
import SpectralRadiusUpperTail.RealGaussianScoreComparison

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

/-- Closed convolution for the actual finite family of independent real Gaussians. -/
theorem realGaussian_finite_normalizer (a : ℝ) (ha : 0 < a)
    (N : ℕ) (v : Fin N → ℝ) (s : ℝ) :
    gaussianFiniteNormalizer standardNormal a v s =
      Real.sqrt (a/(a+2*∑ i, ‖v i‖^2))*Real.exp (-s^2/(a+2*∑ i, ‖v i‖^2)) := by
  have hm : Measurable (fun x : Fin N → ℝ => ∑ i, v i*x i) :=
    measurable_finite_sum _ (fun _ => by fun_prop)
  have hq : 0 ≤ ∑ i, ‖v i‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hi := integral_map (μ := Measure.pi (fun _ : Fin N => standardNormal))
    (φ := fun x => ∑ i, v i*x i) (f := fun x : ℝ => Real.exp (-(s-x)^2/a))
    hm.aemeasurable (by fun_prop)
  rw [realGaussian_finite_sum_law, realGaussian_soft_convolution _ a ha,
    Real.coe_toNNReal _ hq] at hi
  simpa only [gaussianFiniteNormalizer, Real.norm_eq_abs, sq_abs] using hi.symm

/-- Differentiating the closed formula identifies the actual Gaussian score. -/
theorem realGaussian_finite_log_deriv (a : ℝ) (ha : 0 < a)
    (N : ℕ) (v : Fin N → ℝ) (s w : ℝ) :
    deriv (fun t : ℝ => Real.log (gaussianFiniteNormalizer standardNormal a v (s+t • w))) 0 =
      -2*s*w/(a+2*∑ i, ‖v i‖^2) := by
  let d := a+2*∑ i, ‖v i‖^2
  have hd : 0 < d := by dsimp [d]; positivity
  have hc : Real.sqrt (a/d) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (div_pos ha hd))
  have he : (fun t : ℝ => Real.log (gaussianFiniteNormalizer standardNormal a v (s+t • w))) =
      fun t : ℝ => Real.log (Real.sqrt (a/d)) + (-(s+t*w)^2/d) := by
    funext t
    rw [realGaussian_finite_normalizer a ha]
    change Real.log (Real.sqrt (a/d)*Real.exp (-(s+t*w)^2/d)) = _
    rw [Real.log_mul hc (Real.exp_ne_zero _), Real.log_exp]
  rw [he]
  have hp := (((hasDerivAt_id (0 : ℝ)).mul_const w).const_add s).pow 2
  have hh := ((hp.neg.div_const d).const_add (Real.log (Real.sqrt (a/d)))).deriv
  convert! hh using 1 <;> (try simp only [id_eq, zero_mul, add_zero, pow_one, d]) <;> ring

/-- The original real entry assumptions give a compact error bound around the
explicit linear Gaussian score; the comparator is no longer an unevaluated derivative. -/
theorem real_gaussian_linear_score_comparison (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hvar : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (τ : ℝ) (hτ : 0 < τ) (he : Integrable (fun x : ℝ => Real.exp (τ*‖x‖^2)) μ)
    (a : ℝ) (ha : 0 < a) (N : ℕ) (v : Fin N → ℝ) (hv : ∑ i, ‖v i‖^2 ≤ 1)
    (w s : ℝ) (K : ℝ) (hs : ‖s‖ ≤ K) :
    |deriv (fun t : ℝ => Real.log (gaussianFiniteNormalizer μ a v (s+t • w))) 0 +
      2*s*w/(a+2*∑ i, ‖v i‖^2)| ≤
      gaussianScoreComparisonConstant a K*‖w‖*
        ((∫ x : ℝ, ‖x‖^3 ∂μ)+(∫ x : ℝ, ‖x‖^3 ∂standardNormal))*(∑ i, ‖v i‖^3) := by
  have hh := real_gaussian_score_comparison μ hm hvar τ hτ he a ha N v hv w s K hs
  rw [realGaussian_finite_log_deriv a ha] at hh
  convert! hh using 1 <;> congr 1 <;> ring

#print axioms realGaussian_finite_normalizer
#print axioms realGaussian_finite_log_deriv
#print axioms real_gaussian_linear_score_comparison
end SpectralRadiusUpperTail
