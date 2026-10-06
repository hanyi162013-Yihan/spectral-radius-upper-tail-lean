import SpectralRadiusUpperTail.GaussianScoreComparison
import SpectralRadiusUpperTail.ComplexGaussianMoments

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- The compact actual logarithmic-derivative comparison with the actual proper
complex Gaussian follows from the original proper entry assumptions. -/
theorem complex_gaussian_score_comparison (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (τ : ℝ) (hτ : 0 < τ) (he : Integrable (fun x : ℂ => Real.exp (τ*‖x‖^2)) μ)
    (a : ℝ) (ha : 0 < a) (N : ℕ) (v : Fin N → ℂ) (hv : ∑ i, ‖v i‖^2 ≤ 1)
    (w s : ℂ) (K : ℝ) (hs : ‖s‖ ≤ K) :
    |deriv (fun t : ℝ => Real.log (gaussianFiniteNormalizer μ a v (s+t • w))) 0-
      deriv (fun t : ℝ => Real.log (gaussianFiniteNormalizer properComplexGaussian a v (s+t • w))) 0| ≤
      gaussianScoreComparisonConstant a K*‖w‖*
        ((∫ x : ℂ, ‖x‖^3 ∂μ)+(∫ x : ℂ, ‖x‖^3 ∂properComplexGaussian))*(∑ i, ‖v i‖^3) := by
  have hX : MemLp (fun x : ℂ => x) 2 μ :=
    (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr (squareExp_norm_pow_integrable μ τ hτ he 2)
  exact gaussianFinite_score_comparison μ properComplexGaussian hX properComplexGaussian_memLp
    hm properComplexGaussian_mean hvar properComplexGaussian_energy
    (hpseudo.trans properComplexGaussian_pseudo.symm)
    (squareExp_norm_pow_integrable μ τ hτ he 3) properComplexGaussian_third_integrable a ha v hv w s K hs

#print axioms complex_gaussian_score_comparison
end SpectralRadiusUpperTail
