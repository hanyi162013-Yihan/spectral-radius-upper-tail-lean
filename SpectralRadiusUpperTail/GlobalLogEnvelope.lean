import SpectralRadiusUpperTail.ExponentialVariation
import SpectralRadiusUpperTail.WeightedSquareExpMoment
import SpectralRadiusUpperTail.SoftNormalizer

namespace SpectralRadiusUpperTail
open MeasureTheory

lemma global_log_young (C u e d r D : ℝ) (hC : 0 ≤ C) (hu : 0 ≤ u)
    (he : 0 ≤ e) (hd : 0 < d) (hr : 0 ≤ r) (hsmall : C*e ≤ d)
    (hD : |D| ≤ C*u*r+C*e*r^2) :
    |D| ≤ C^2*u^2/(4*d)+2*d*r^2 := by
  have hy : C*u*r ≤ C^2*u^2/(4*d)+d*r^2 := by
    have hh := sq_nonneg (2*d*r-C*u)
    have hh' : C*u*r-d*r^2 ≤ C^2*u^2/(4*d) := by
      apply (le_div_iff₀ (show 0 < 4*d by positivity)).mpr
      nlinarith only [hh]
    linarith only [hh']
  have hs := mul_le_mul_of_nonneg_right hsmall (sq_nonneg r)
  nlinarith only [hD, hy, hs]

lemma global_exp_variation_weight (C u e d r D : ℝ) (hC : 0 ≤ C) (hu : 0 ≤ u)
    (he : 0 ≤ e) (heu : e ≤ u) (hd : 0 < d) (hr : 0 ≤ r) (hsmall : C*e ≤ d)
    (hD : |D| ≤ C*u*r+C*e*r^2) :
    r*|Real.exp D-1| ≤
      (C*u*Real.exp (C^2*u^2/(4*d)))*((r^2+r^3)*Real.exp (2*d*r^2)) := by
  have hp : r*|D| ≤ C*u*(r^2+r^3) := by
    have h := mul_le_mul_of_nonneg_left hD hr
    have h' := mul_le_mul_of_nonneg_left heu (show 0 ≤ C*r^3 by positivity)
    nlinarith only [h, h']
  have hx : Real.exp |D| ≤ Real.exp (C^2*u^2/(4*d))*Real.exp (2*d*r^2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (global_log_young C u e d r D hC hu he hd hr hsmall hD)
  calc
    _ ≤ (r*|D|)*Real.exp |D| := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (abs_exp_sub_one_le_abs_mul_exp_abs D) hr
    _ ≤ (C*u*(r^2+r^3))*(Real.exp (C^2*u^2/(4*d))*Real.exp (2*d*r^2)) :=
      mul_le_mul hp hx (Real.exp_nonneg _) (by positivity)
    _ = _ := by ring

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

/-- A global logarithmic perturbation has an integrable exponential density.
Only its quadratic coefficient must be small; u is unrestricted. -/
theorem global_log_exp_integrable (μ : Measure E) [IsProbabilityMeasure μ]
    (D : E → ℝ) (hDm : Measurable D) (C u e d : ℝ)
    (hC : 0 ≤ C) (hu : 0 ≤ u) (he : 0 ≤ e) (hd : 0 < d) (hsmall : C*e ≤ d)
    (hD : ∀ x, |D x| ≤ C*u*‖x‖+C*e*‖x‖^2)
    (hexp : Integrable (fun x : E => Real.exp (4*d*‖x‖^2)) μ) :
    Integrable (fun x => Real.exp (D x)) μ := by
  apply (hexp.const_mul (Real.exp (C^2*u^2/(4*d)))).mono_nonneg
    (Real.measurable_exp.comp hDm).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun _ => Real.exp_nonneg _))
  apply Filter.Eventually.of_forall
  intro x
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := global_log_young C u e d ‖x‖ (D x) hC hu he hd (norm_nonneg x) hsmall (hD x)
  have hn := le_abs_self (D x)
  nlinarith [sq_nonneg ‖x‖]

/-- Jensen supplies a target-dependent positive denominator without requiring
the likelihood to be uniformly close to one. -/
theorem global_log_normalizer_lower (μ : Measure E) [IsProbabilityMeasure μ]
    (D : E → ℝ) (hDm : Measurable D) (C u e d : ℝ)
    (hC : 0 ≤ C) (hu : 0 ≤ u) (he : 0 ≤ e) (heu : e ≤ u)
    (hd : 0 < d) (hsmall : C*e ≤ d)
    (hD : ∀ x, |D x| ≤ C*u*‖x‖+C*e*‖x‖^2)
    (hvar : (∫ x : E, ‖x‖^2 ∂μ) = 1)
    (hexp : Integrable (fun x : E => Real.exp (4*d*‖x‖^2)) μ) :
    Real.exp (-3*C*u) ≤ ∫ x, Real.exp (D x) ∂μ := by
  have hi2 := squareExp_norm_pow_integrable μ (4*d) (by positivity) hexp 2
  have henv : Integrable (fun x : E => C*u*(1+2*‖x‖^2)) μ :=
    ((integrable_const 1).add (hi2.const_mul 2)).const_mul (C*u)
  have hb (x : E) : |D x| ≤ C*u*(1+2*‖x‖^2) := by
    have h := hD x
    have h' := mul_le_mul_of_nonneg_left heu (show 0 ≤ C*‖x‖^2 by positivity)
    have hr : ‖x‖ ≤ 1+‖x‖^2 := by nlinarith [sq_nonneg (‖x‖-1)]
    have h'' := mul_le_mul_of_nonneg_left hr (mul_nonneg hC hu)
    nlinarith only [h, h', h'']
  have hiD : Integrable D μ := henv.mono' hDm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x))
  have hiE := global_log_exp_integrable μ D hDm C u e d hC hu he hd hsmall hD hexp
  have hlow : -3*C*u ≤ ∫ x, D x ∂μ := by
    have h := integral_mono henv.neg hiD (fun x => neg_le_of_abs_le (hb x))
    have hv : (∫ x : E, C*u*(1+2*‖x‖^2) ∂μ) = 3*C*u := by
      rw [integral_const_mul, integral_add (integrable_const 1) (hi2.const_mul 2),
        integral_const_mul, hvar]
      have huniv : μ.real Set.univ = (1 : ℝ) := by simp
      simp only [integral_const, smul_eq_mul, huniv]
      ring
    have h' : (∫ x : E, -(C*u*(1+2*‖x‖^2)) ∂μ) ≤ ∫ x, D x ∂μ := by
      convert! h using 1
    rw [integral_neg, hv] at h'
    convert! h' using 1 <;> ring
  have hj := convexOn_exp.map_integral_le (μ := μ) Real.continuous_exp.continuousOn
    isClosed_univ (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) hiD hiE
  exact (Real.exp_le_exp.mpr hlow).trans hj

#print axioms global_log_normalizer_lower
end SpectralRadiusUpperTail
