import SpectralRadiusUpperTail.GaussianSquareMoment
import SpectralRadiusUpperTail.GaussianExactMoments
import Mathlib.MeasureTheory.Integral.Prod

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Gaussian linearization derives both square-exponential integrability and a
uniform bound from the actual MGF inequalities. Product integrability is proved
before applying Fubini. -/
theorem mgf_gaussian_linearization (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) (K α : ℝ)
    (hmgf : ∀ t : ℝ, Integrable (fun x => Real.exp (t*X x)) μ ∧
      (∫ x, Real.exp (t*X x) ∂μ) ≤ Real.exp (K*t^2))
    (hα : K*α^2 ≤ 1/4) :
    Integrable (fun x => Real.exp (α^2*(X x)^2/2)) μ ∧
      (∫ x, Real.exp (α^2*(X x)^2/2) ∂μ) ≤ 2 := by
  let F := fun z : ℝ × Ω => Real.exp (α*z.1*X z.2)
  have hF : Measurable F := Real.measurable_exp.comp
    ((measurable_const.mul measurable_fst).mul (hX.comp measurable_snd))
  have hbound (g : ℝ) : (∫ x, F (g,x) ∂μ) ≤ Real.exp (g^2/4) := by
    apply (hmgf (α*g)).2.trans
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right hα (sq_nonneg g)
    nlinarith only [h]
  have hn (g : ℝ) : (∫ x, ‖F (g,x)‖ ∂μ) ≤ Real.exp (g^2/4) := by
    simpa only [F, Real.norm_eq_abs, Real.abs_exp] using hbound g
  have hFn : ∀ z, 0 ≤ F z := fun _ => Real.exp_nonneg _
  have hFi : Integrable F (standardNormal.prod μ) := by
    apply (integrable_prod_iff hF.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall (fun g => (hmgf (α*g)).1), ?_⟩
    apply standardNormal_exp_quarter_sq.1.mono_nonneg
      hF.stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun g => integral_nonneg (fun x => norm_nonneg _))
    · exact Filter.Eventually.of_forall hn
  have hinner (x : Ω) : (∫ g, F (g,x) ∂standardNormal) = Real.exp (α^2*(X x)^2/2) := by
    have he (g : ℝ) : α*g*X x = (α*X x)*g := by ring
    simp_rw [F, he]
    change mgf id standardNormal (α*X x) = _
    rw [standardNormal_mgf_eq]
    congr 1
    ring
  have hi := hFi.integral_prod_right
  simp_rw [hinner] at hi
  refine ⟨hi, ?_⟩
  calc
    _ = ∫ x, ∫ g, F (g,x) ∂standardNormal ∂μ := by simp_rw [hinner]
    _ = ∫ g, ∫ x, F (g,x) ∂μ ∂standardNormal :=
      (integral_integral_swap (f := fun g x => F (g,x)) hFi).symm
    _ ≤ ∫ g : ℝ, Real.exp (g^2/4) ∂standardNormal :=
      integral_mono hFi.integral_prod_left standardNormal_exp_quarter_sq.1 hbound
    _ ≤ 2 := standardNormal_exp_quarter_sq.2

/-- A concrete positive exponent, chosen without square roots. -/
theorem quadratic_mgf_squareExp (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) (K : ℝ) (hK : 0 ≤ K)
    (hmgf : ∀ t : ℝ, Integrable (fun x => Real.exp (t*X x)) μ ∧
      (∫ x, Real.exp (t*X x) ∂μ) ≤ Real.exp (K*t^2)) :
    let c := (1/(2*(K+1)))^2/2
    0 < c ∧ Integrable (fun x => Real.exp (c*(X x)^2)) μ ∧
      (∫ x, Real.exp (c*(X x)^2) ∂μ) ≤ 2 := by
  have hden : 0 < 4*(K+1)^2 := by positivity
  have he : K*(1/(2*(K+1)))^2 = K/(4*(K+1)^2) := by
    have hK1 : K+1 ≠ 0 := by positivity
    field_simp <;> ring
  have hα : K*(1/(2*(K+1)))^2 ≤ 1/4 := by
    rw [he]
    apply (div_le_iff₀ hden).mpr
    nlinarith [sq_nonneg K]
  have hh := mgf_gaussian_linearization μ X hX K (1/(2*(K+1))) hmgf hα
  have hfun : (fun x => Real.exp ((1/(2*(K+1)))^2/2*(X x)^2)) =
      (fun x => Real.exp ((1/(2*(K+1)))^2*(X x)^2/2)) := by
    funext x
    congr 1
    ring
  dsimp only
  refine ⟨by positivity, ?_⟩
  rw [hfun]
  exact hh

#print axioms quadratic_mgf_squareExp
end SpectralRadiusUpperTail
