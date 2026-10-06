import SpectralRadiusUpperTail.ComplexGaussianConvolution
import SpectralRadiusUpperTail.ComplexGaussianSumLaw
import SpectralRadiusUpperTail.ComplexGaussianScoreComparison

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Closed convolution for an actual finite family of independent proper complex Gaussians. -/
theorem properComplexGaussian_finite_normalizer (a : ℝ) (ha : 0 < a)
    (N : ℕ) (v : Fin N → ℂ) (s : ℂ) :
    gaussianFiniteNormalizer properComplexGaussian a v s =
      (a/(a+∑ i, ‖v i‖^2))*Real.exp (-‖s‖^2/(a+∑ i, ‖v i‖^2)) := by
  have hm : Measurable (fun x : Fin N → ℂ => ∑ i, v i*x i) :=
    measurable_finite_sum _ (fun _ => by fun_prop)
  have hq : 0 ≤ ∑ i, ‖v i‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hi := integral_map (μ := Measure.pi (fun _ : Fin N => properComplexGaussian))
    (φ := fun x => ∑ i, v i*x i) (f := fun x : ℂ => Real.exp (-‖s-x‖^2/a))
    hm.aemeasurable (by fun_prop)
  rw [properComplexGaussian_finite_sum_law, properComplexGaussian_soft_convolution _ a hq ha] at hi
  exact hi.symm

/-- The actual complex Gaussian logarithmic derivative is the isotropic linear score. -/
theorem properComplexGaussian_finite_log_deriv (a : ℝ) (ha : 0 < a)
    (N : ℕ) (v : Fin N → ℂ) (s w : ℂ) :
    deriv (fun t : ℝ => Real.log (gaussianFiniteNormalizer properComplexGaussian a v (s+t • w))) 0 =
      -2*inner ℝ s w/(a+∑ i, ‖v i‖^2) := by
  let d := a+∑ i, ‖v i‖^2
  have hd : 0 < d := by dsimp [d]; positivity
  have hc : a/d ≠ 0 := ne_of_gt (div_pos ha hd)
  have he : (fun t : ℝ => Real.log (gaussianFiniteNormalizer properComplexGaussian a v (s+t • w))) =
      fun t : ℝ => Real.log (a/d) + (-‖s+t • w‖^2/d) := by
    funext t
    rw [properComplexGaussian_finite_normalizer a ha]
    change Real.log ((a/d)*Real.exp (-‖s+t • w‖^2/d)) = _
    rw [Real.log_mul hc (Real.exp_ne_zero _), Real.log_exp]
  rw [he]
  have hline : HasDerivAt (fun t : ℝ => s+t • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add s
  have hh := ((hline.norm_sq.neg.div_const d).const_add (Real.log (a/d))).deriv
  convert! hh using 1 <;> (try simp only [zero_smul, add_zero, d]) <;> ring

/-- Compact approximation by the explicit linear score for the original proper
complex entry law, without coordinate independence or symmetry assumptions. -/
theorem complex_gaussian_linear_score_comparison (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (τ : ℝ) (hτ : 0 < τ) (he : Integrable (fun x : ℂ => Real.exp (τ*‖x‖^2)) μ)
    (a : ℝ) (ha : 0 < a) (N : ℕ) (v : Fin N → ℂ) (hv : ∑ i, ‖v i‖^2 ≤ 1)
    (w s : ℂ) (K : ℝ) (hs : ‖s‖ ≤ K) :
    |deriv (fun t : ℝ => Real.log (gaussianFiniteNormalizer μ a v (s+t • w))) 0 +
      2*inner ℝ s w/(a+∑ i, ‖v i‖^2)| ≤
      gaussianScoreComparisonConstant a K*‖w‖*
        ((∫ x : ℂ, ‖x‖^3 ∂μ)+(∫ x : ℂ, ‖x‖^3 ∂properComplexGaussian))*(∑ i, ‖v i‖^3) := by
  have hh := complex_gaussian_score_comparison μ hm hvar hpseudo τ hτ he a ha N v hv w s K hs
  rw [properComplexGaussian_finite_log_deriv a ha] at hh
  convert! hh using 1 <;> congr 1 <;> ring

#print axioms properComplexGaussian_finite_normalizer
#print axioms properComplexGaussian_finite_log_deriv
#print axioms complex_gaussian_linear_score_comparison
end SpectralRadiusUpperTail
