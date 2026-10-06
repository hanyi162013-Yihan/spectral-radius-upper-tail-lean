import SpectralRadiusUpperTail.HaarSphereIntegral
import SpectralRadiusUpperTail.GaussianLinearIntegral
import SpectralRadiusUpperTail.GaussianBallNormalizer

namespace SpectralRadiusUpperTail
open MeasureTheory Metric
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

lemma spherical_gaussian_determinant_bound (μ : Measure E) [μ.IsAddHaarMeasure]
    (A : E →ₗ[ℝ] E) (hA : LinearMap.det A ≠ 0) :
    (∫⁻ v : sphere (0 : E) 1, ENNReal.ofReal (Real.exp (-‖A v.val‖^2)) ∂haarSphereProbability μ) ≤
      ENNReal.ofReal |(LinearMap.det A)⁻¹| *
        ENNReal.ofReal (Real.Gamma ((Module.finrank ℝ E : ℝ)/2+1)) := by
  have hm : Measurable (fun x : E => ENNReal.ofReal (Real.exp (-‖A x‖^2))) :=
    (Real.continuous_exp.comp (A.continuous_of_finiteDimensional.norm.pow 2).neg).measurable.ennreal_ofReal
  have hh := sphere_integral_mul_ball_le μ _ hm (by
    intro v r hr hr1
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    simp only [map_smul,norm_smul,Real.norm_eq_abs,abs_of_pos hr,mul_pow]
    have hr2 : r^2 ≤ 1 := by nlinarith
    have hb := mul_le_of_le_one_left (sq_nonneg ‖A v.val‖) hr2
    linarith)
  have hV0 : μ (ball (0 : E) 1) ≠ 0 := isOpen_ball.measure_ne_zero μ (nonempty_ball.mpr zero_lt_one)
  have hVtop : μ (ball (0 : E) 1) ≠ ∞ := ne_of_lt measure_ball_lt_top
  have hb := (ENNReal.le_div_iff_mul_le (Or.inl hV0) (Or.inl hVtop)).mpr hh
  have hg := gaussian_linear_lintegral μ A hA 1
  simp only [neg_mul,one_mul] at hg
  rw [hg,mul_div_assoc,gaussian_ball_normalizer_ratio] at hb
  exact hb

#print axioms spherical_gaussian_determinant_bound
end SpectralRadiusUpperTail
