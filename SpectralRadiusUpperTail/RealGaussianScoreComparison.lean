import SpectralRadiusUpperTail.GaussianScoreComparison
import SpectralRadiusUpperTail.RealGaussianReplacement

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- A compact bound for the actual directional logarithmic derivative against
its actual standard real Gaussian comparator, from the original entry assumptions. -/
theorem real_gaussian_score_comparison (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hvar : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (τ : ℝ) (hτ : 0 < τ) (he : Integrable (fun x : ℝ => Real.exp (τ*‖x‖^2)) μ)
    (a : ℝ) (ha : 0 < a) (N : ℕ) (v : Fin N → ℝ) (hv : ∑ i, ‖v i‖^2 ≤ 1)
    (w s : ℝ) (K : ℝ) (hs : ‖s‖ ≤ K) :
    |deriv (fun t : ℝ => Real.log (gaussianFiniteNormalizer μ a v (s+t • w))) 0-
      deriv (fun t : ℝ => Real.log (gaussianFiniteNormalizer standardNormal a v (s+t • w))) 0| ≤
      gaussianScoreComparisonConstant a K*‖w‖*
        ((∫ x : ℝ, ‖x‖^3 ∂μ)+(∫ x : ℝ, ‖x‖^3 ∂standardNormal))*(∑ i, ‖v i‖^3) := by
  have hX : MemLp (fun x : ℝ => x) 2 μ :=
    (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr (squareExp_norm_pow_integrable μ τ hτ he 2)
  have hG : MemLp (fun x : ℝ => x) 2 standardNormal := by
    convert! (memLp_id_gaussianReal' (μ := 0) (v := 1) (2 : ℝ≥0∞) (by norm_num)) using 1
  have hmG : (∫ x : ℝ, x ∂standardNormal) = 0 := by
    simpa using standardNormal_odd_moment 0
  have hvG : (∫ x : ℝ, ‖x‖^2 ∂standardNormal) = 1 := by
    simpa only [Real.norm_eq_abs, sq_abs] using standardNormal_second_moment
  have hpμ : (∫ x : ℝ, x^2 ∂μ) = 1 := by
    simpa only [Real.norm_eq_abs, sq_abs] using hvar
  have h3G : Integrable (fun x : ℝ => ‖x‖^3) standardNormal := by
    simpa only [norm_pow] using (standardNormal_pow_integrable 3).norm
  exact gaussianFinite_score_comparison μ standardNormal hX hG hm hmG hvar hvG
    (hpμ.trans standardNormal_second_moment.symm) (squareExp_norm_pow_integrable μ τ hτ he 3)
    h3G a ha v hv w s K hs

#print axioms real_gaussian_score_comparison
end SpectralRadiusUpperTail
