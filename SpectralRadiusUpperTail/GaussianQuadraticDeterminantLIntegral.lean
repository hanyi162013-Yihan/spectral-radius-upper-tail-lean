import SpectralRadiusUpperTail.GaussianQuadraticDeterminantMoment
import SpectralRadiusUpperTail.FiniteGaussianRawIntegral

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix

theorem real_quadratic_det_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (x y : ℝ) :
    0 ≤ ((H-x • 1)^2+y^2 • 1).det := by
  rw [real_quadratic_det_eq_charpoly_normSq]
  exact Complex.normSq_nonneg _

theorem gaussian_real_quadratic_det_lintegral
    {ι : Type*} [Fintype ι] [DecidableEq ι] (x y : ℝ) :
    (∫⁻ a : ι × ι → ℝ,
      ENNReal.ofReal (((Matrix.of a.curry-x • 1)^2+y^2 • 1).det)
      ∂Measure.pi (fun _ => standardNormal)) =
      ENNReal.ofReal (((Fintype.card ι).factorial : ℝ)*
        ginibreExpPartial (Fintype.card ι+1) (x^2+y^2)) := by
  have hi : Integrable (fun a : ι × ι → ℝ =>
      ((Matrix.of a.curry-x • 1)^2+y^2 • 1).det)
      (Measure.pi (fun _ => standardNormal)) := by
    simp_rw [real_quadratic_det_eq_charpoly_normSq]
    exact (gaussian_real_complex_charpoly_second_moment
      ((x : ℂ)+(y : ℂ)*Complex.I)).1
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun a => real_quadratic_det_nonneg _ x y)),
    gaussian_real_quadratic_det_poisson_moment]

noncomputable def realMatrixRawGaussianMass (ι : Type*) [Fintype ι] : ℝ≥0∞ :=
  ∫⁻ a : ι × ι → ℝ, ENNReal.ofReal (Real.exp (-(∑ p, (a p)^2)/2))

theorem gaussian_real_quadratic_det_raw_lintegral
    {ι : Type*} [Fintype ι] [DecidableEq ι] (x y : ℝ) :
    (∫⁻ a : ι × ι → ℝ,
      ENNReal.ofReal (Real.exp (-(∑ p, (a p)^2)/2))*
        ENNReal.ofReal (((Matrix.of a.curry-x • 1)^2+y^2 • 1).det)) =
      realMatrixRawGaussianMass ι*
        ENNReal.ofReal (((Fintype.card ι).factorial : ℝ)*
          ginibreExpPartial (Fintype.card ι+1) (x^2+y^2)) := by
  rw [finiteGaussian_raw_lintegral]
  · rw [gaussian_real_quadratic_det_lintegral]
    rfl
  · apply Measurable.ennreal_ofReal
    have hc : Continuous (fun a : ι × ι → ℝ => Matrix.of a.curry) :=
      continuous_pi (fun i => continuous_pi (fun j => continuous_apply (i,j)))
    exact (((hc.sub continuous_const).pow 2).add continuous_const).matrix_det.measurable

#print axioms real_quadratic_det_nonneg
#print axioms gaussian_real_quadratic_det_lintegral
#print axioms gaussian_real_quadratic_det_raw_lintegral
end SpectralRadiusUpperTail
