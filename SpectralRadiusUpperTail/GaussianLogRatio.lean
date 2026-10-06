import SpectralRadiusUpperTail.GaussianScoreGrowth
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Abel

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma linear_derivative_growth_increment (f : E → ℝ) (f' : E → E →L[ℝ] ℝ)
    (hf : ∀ x, HasFDerivAt f (f' x) x) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ x, ‖f' x‖ ≤ C*(1+‖x‖)) (s h : E) :
    |f (s-h)-f s| ≤ C*‖h‖*(1+‖s‖+‖h‖) := by
  have hbound : ∀ x ∈ Metric.closedBall s ‖h‖, ‖f' x‖ ≤ C*(1+‖s‖+‖h‖) := by
    intro x hx
    have hx' : ‖x-s‖ ≤ ‖h‖ := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
    have hxn : ‖x‖ ≤ ‖s‖+‖h‖ := by
      have ht := norm_add_le (x-s) s
      rw [sub_add_cancel] at ht
      linarith
    exact (hb x).trans (mul_le_mul_of_nonneg_left (by linarith) hC)
  have hs : s ∈ Metric.closedBall s ‖h‖ := by simp
  have hh : s-h ∈ Metric.closedBall s ‖h‖ := by
    have heq : s-h-s = -h := by abel
    simp only [Metric.mem_closedBall, dist_eq_norm, heq, norm_neg, le_refl]
  have hv := (convex_closedBall s ‖h‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x _ => (hf x).hasFDerivWithinAt) hbound hs hh
  have heq : s-h-s = -h := by abel
  rw [Real.norm_eq_abs, heq, norm_neg] at hv
  nlinarith only [hv]

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The actual Gaussian log-density increment is bounded by the displacement
times a linear function of the starting point and displacement. -/
theorem gaussian_log_increment (μ : Measure E) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : E => x) 2 μ) (hm : (∫ x : E, x ∂μ) = 0)
    (hvar : (∫ x : E, ‖x‖^2 ∂μ) ≤ 1) (a c L : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hLn : 0 ≤ L)
    (hexp : Integrable (fun x : E => Real.exp (c*‖x‖^2)) μ)
    (hL : (∫ x : E, Real.exp (c*‖x‖^2) ∂μ) ≤ Real.exp L) :
    ∀ s h : E,
      |Real.log (gaussianConvolution μ a (s-h))-Real.log (gaussianConvolution μ a s)| ≤
        gaussianScoreConstant a c L*‖h‖*(1+‖s‖+‖h‖) := by
  obtain ⟨hC, hscore⟩ := gaussian_log_score_growth μ hX hm hvar a c L ha hc hLn hexp hL
  intro s h
  exact linear_derivative_growth_increment _ _ (fun x => (hscore x).1)
    (gaussianScoreConstant a c L) hC
    (fun x => (hscore x).2) s h

#print axioms gaussian_log_increment
end SpectralRadiusUpperTail
