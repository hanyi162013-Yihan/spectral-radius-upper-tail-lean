import SpectralRadiusUpperTail.GaussianFiniteSumLaw
import SpectralRadiusUpperTail.ComplexRowCovariance

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- An actual finite weighted sum of independent proper complex Gaussians has
the same law as a single proper complex Gaussian scaled by the square root of
the coefficient energy. Zero energy and empty sums are included. -/
theorem properComplexGaussian_finite_sum_law (N : ℕ) (v : Fin N → ℂ) :
    (Measure.pi (fun _ : Fin N => properComplexGaussian)).map (fun x => ∑ i, v i*x i) =
      scalarPushforward properComplexGaussian ((Real.sqrt (∑ i, ‖v i‖^2) : ℝ) : ℂ) := by
  let c : ℂ := (Real.sqrt (∑ i, ‖v i‖^2) : ℝ)
  let ν := scalarPushforward properComplexGaussian c
  haveI : IsGaussian ν := scalarPushforward_isGaussian _ _
  have hc : ‖c‖^2 = ∑ i, ‖v i‖^2 := by
    simp only [c, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hm (s : ℂ) : (∫ x : ℂ, inner ℝ s x ∂ν) = 0 := by
    have hi := (scalarPushforward_memLp _ c properComplexGaussian_memLp).integrable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    rw [integral_inner hi]
    rw [scalarPushforward_mean, properComplexGaussian_mean, mul_zero, inner_zero_right]
  have hv (s : ℂ) : variance (fun x : ℂ => inner ℝ s x) ν =
      ‖s‖^2*(∑ i, ‖v i‖^2)/2 := by
    rw [variance_eq_integral (by fun_prop), hm]
    simp only [sub_zero]
    change (∫ x : ℂ, (inner ℝ s x)^2 ∂scalarPushforward properComplexGaussian c) = _
    rw [scalarPushforward, integral_map (by fun_prop) (by fun_prop)]
    rw [proper_complex_weighted_projection _ properComplexGaussian_memLp
      properComplexGaussian_energy properComplexGaussian_pseudo, hc]
  change _ = ν
  apply Measure.ext_of_charFun
  funext s
  rw [(gaussianFinite_sum_hasGaussianLaw properComplexGaussian N v).charFun_map_eq,
    IsGaussian.charFun_eq, integral_complex_ofReal, hm, hv,
    proper_complex_row_projection_mean _ properComplexGaussian_memLp properComplexGaussian_mean,
    proper_complex_row_projection_variance _ properComplexGaussian_memLp properComplexGaussian_mean
      properComplexGaussian_energy properComplexGaussian_pseudo]

#print axioms properComplexGaussian_finite_sum_law
end SpectralRadiusUpperTail
