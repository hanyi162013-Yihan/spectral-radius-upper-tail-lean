import SpectralRadiusUpperTail.RealMomentClass
import SpectralRadiusUpperTail.GaussianSquareMoment
import Mathlib.Analysis.SpecialFunctions.Exponential

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

/-- Tonelli expansion, valid before exponential integrability is known. -/
lemma even_moment_expansion (μ : Measure ℝ)
    (hint : ∀ m : ℕ, Integrable (fun x : ℝ => x^(2*m)) μ)
    (c : ℝ) (hc : 0 ≤ c) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (c*x^2)) ∂μ) =
      ∑' m : ℕ, ENNReal.ofReal ((c^m/(m.factorial : ℝ)) * (∫ x : ℝ, x^(2*m) ∂μ)) := by
  have he (x : ℝ) : ENNReal.ofReal (Real.exp (c*x^2)) =
      ∑' m : ℕ, ENNReal.ofReal ((c*x^2)^m/(m.factorial : ℝ)) := by
    have hs := NormedSpace.expSeries_div_hasSum_exp (c*x^2)
    rw [← Real.exp_eq_exp_ℝ] at hs
    rw [← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hs.summable]
  simp_rw [he]
  rw [lintegral_tsum (fun m => by fun_prop)]
  apply tsum_congr
  intro m
  have hp (x : ℝ) : (c*x^2)^m/(m.factorial : ℝ) =
      (c^m/(m.factorial : ℝ))*x^(2*m) := by
    rw [mul_pow, ← pow_mul]
    ring
  simp_rw [hp]
  rw [← ofReal_integral_eq_lintegral_ofReal ((hint m).const_mul _)
    (Filter.Eventually.of_forall (fun x => by
      change 0 ≤ (c^m/(m.factorial : ℝ))*x^(2*m)
      rw [pow_mul]
      positivity)), integral_const_mul]

/-- Gaussian even-moment domination alone gives a finite square-exponential
moment; symmetry is not needed for this step. -/
theorem dominated_even_squareExp (μ : Measure ℝ)
    (h : GaussianEvenMomentDomination μ) :
    Integrable (fun x : ℝ => Real.exp (x^2/4)) μ ∧
      (∫ x : ℝ, Real.exp (x^2/4) ∂μ) ≤ 2 := by
  have hb : (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (x^2/4)) ∂μ) ≤
      ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (x^2/4)) ∂standardNormal := by
    have he (x : ℝ) : x^2/4 = (1/4)*x^2 := by ring
    simp_rw [he]
    rw [even_moment_expansion μ (fun m => (h m).1) (1/4) (by norm_num),
      even_moment_expansion standardNormal (fun m => standardNormal_pow_integrable (2*m))
        (1/4) (by norm_num)]
    apply ENNReal.tsum_le_tsum
    intro m
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (h m).2 (by positivity))
  have hg := standardNormal_exp_quarter_sq
  rw [← ofReal_integral_eq_lintegral_ofReal hg.1
    (Filter.Eventually.of_forall (fun _ => Real.exp_nonneg _))] at hb
  have hf : Integrable (fun x : ℝ => Real.exp (x^2/4)) μ := by
    refine ⟨by fun_prop, ?_⟩
    apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
      (fun x : ℝ => Real.exp_nonneg (x^2/4)))).mpr
    exact lt_of_le_of_lt hb ENNReal.ofReal_lt_top
  refine ⟨hf, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hf
    (Filter.Eventually.of_forall (fun _ => Real.exp_nonneg _))] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 2)).mp
    (hb.trans (ENNReal.ofReal_le_ofReal hg.2))

#print axioms even_moment_expansion
#print axioms dominated_even_squareExp
end SpectralRadiusUpperTail
