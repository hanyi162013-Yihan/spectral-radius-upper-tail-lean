import SpectralRadiusUpperTail.ComplexPointBulkLower
import SpectralRadiusUpperTail.ComplexPointLikelihood
import SpectralRadiusUpperTail.ComplexLocalTilt
import SpectralRadiusUpperTail.ComplexLocalParameters
import SpectralRadiusUpperTail.ComplexMatrixTiltException
import SpectralRadiusUpperTail.ProbabilityEventComparison
import SpectralRadiusUpperTail.TalagrandClassConsequences

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology ENNReal

lemma complex_point_bulk_lower_deviation
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℂ => Real.exp (c*‖x‖^2)) μ)
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hv : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (b : ℂ) (hb : 1 < ‖b‖) (s : ℝ) (hs : 0 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ q : ℝ, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
      (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        {x | regularizedResidualLogDet x b (s*s)/(n : ℝ) < 2*Real.log ‖b‖-s} ≤
          C*Real.exp (-q*(n : ℝ)^2) := by
  have h2 := squareExp_norm_pow_integrable μ c hc hexp 2
  have hconv := cutoff_concentration_transfer μ c hc hexp h2 (cutoff_convex_concentration_proved μ)
  obtain ⟨C, hC, q, hq, hbad⟩ := complex_bulk_concentration_of_convex_concentration μ h2 hconv
    (s*s) (s/2) (mul_pos hs hs) (by positivity)
  have hmean := complex_point_bulk_logDet_mean_lower μ c hc hexp hm hv
    b (s*s) (s/2) hb (mul_pos hs hs) (by positivity)
  refine ⟨C, hC, q, hq, ?_⟩
  filter_upwards [hmean, hbad] with n hn hbn
  exact (lower_event_le_centered_event _ _ (2*Real.log ‖b‖) s hn).trans (hbn b)

/-- The universal lower rate near any prescribed complex exterior point.
The disk can be arbitrarily small; no invariance of the entry law is assumed. -/
theorem complex_point_exponential_lower
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hv : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hp : (∫ x : ℂ, x^2 ∂μ) = 0)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℂ => Real.exp (4*c*‖x‖^2)) μ)
    (w : ℂ) (hw : 1 < ‖w‖) (δ : ℝ) (hδ : 0 < δ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Real.exp ((n : ℝ)*(-rate 2 ‖w‖-ε)) ≤
      (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        (complexLocalEigenvalueEvent n w δ) := by
  obtain ⟨s, hs, hcost⟩ := complex_point_tilt_parameters ‖w‖ (ε/2) (by linarith) (by positivity)
  let b : ℂ := ((s+1 : ℝ) : ℂ)*w
  have hbcenter : b/((s+1 : ℝ) : ℂ) = w := by
    dsimp [b]
    have hne : ((s+1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (show s+1 ≠ 0 by positivity)
    field_simp
  have hbnorm : ‖b‖ = (s+1)*‖w‖ := by
    simp only [b, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < s+1)]
  have hb : 1 < ‖b‖ := by rw [hbnorm]; nlinarith
  obtain ⟨L, hL, hweight⟩ := complex_point_likelihood_cost_on_bulk μ hm hv hp
    (4*c) (by positivity) hexp s s s s b hs hs hs hs
  let ν : (n : ℕ) → Measure (flatUnitDirections ℂ n L) := fun n => haarFlatPrior ℂ n L hL
  letI : ∀ n, IsProbabilityMeasure (ν n) := fun n => haarFlatPrior_probability ℂ n L hL
  let E := fun n => {x : Fin n → Fin n → ℂ |
    regularizedResidualLogDet x b (s*s)/(n : ℝ) < 2*Real.log ‖b‖-s}
  have hE (n : ℕ) : MeasurableSet (E n) :=
    measurableSet_lt ((regularizedResidualLogDet_measurable n b (s*s)).div_const _) measurable_const
  obtain ⟨C, hC, q, hq, hbad⟩ := complex_point_bulk_lower_deviation μ
    (4*c) (by positivity) hexp hm hv b hb s hs
  have ht := complex_spectralTilt_quadratic_exception μ hm hv hp (4*c) (by positivity) hexp
    s hs L (by linarith) ν b E hE C q hC hq hbad
  letI : ∀ n, IsProbabilityMeasure (flatSpectralMatrixTilt μ (ν n) s b) :=
    fun n => flatSpectralMatrixTilt_probability μ (ν n) s hs b
  have hcostprob : Tendsto (fun n => (flatSpectralMatrixTilt μ (ν n) s b).real
      {x | ENNReal.ofReal (Real.exp ((n : ℝ)*lowerTiltCost 2 ‖b‖ s (s+s) s (2*s))) <
        flatSpectralMatrixLikelihood μ (ν n) s b x}) atTop (𝓝 0) := by
    apply probability_tendsto_zero_of_eventual_subset (fun n => Fin n → Fin n → ℂ)
      (fun n => flatSpectralMatrixTilt μ (ν n) s b) _ E _ ht
    filter_upwards [hweight] with n hn
    intro x hx
    by_contra hnot
    exact (not_lt_of_ge (hn x (le_of_not_gt hnot))) hx
  have hlo := complex_local_exponential_lower_of_likelihood_cost μ hm hv hp c hc hexp
    s L hs hL ν b (by simpa only [hbcenter] using hw) δ hδ
    (lowerTiltCost 2 ‖b‖ s (s+s) s (2*s)) hcostprob (ε/2) (by positivity)
  rw [hbcenter] at hlo
  filter_upwards [hlo] with n hn
  apply le_trans (Real.exp_le_exp.mpr ?_) hn
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
  rw [hbnorm, show s+s = 2*s by ring]
  linarith

#print axioms complex_point_bulk_lower_deviation
#print axioms complex_point_exponential_lower
end SpectralRadiusUpperTail
