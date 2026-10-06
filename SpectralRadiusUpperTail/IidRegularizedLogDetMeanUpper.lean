import SpectralRadiusUpperTail.IidRegularizedLogDetUpperProbability
import SpectralRadiusUpperTail.IidRegularizedLogDetSecondMoment
import SpectralRadiusUpperTail.UpperMeanLimit

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

lemma iid_regularizedLogDet_mean_upper (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (b : ℝ) (hb : 1 < b) :
    ∃ M : ℝ, 0 < M ∧ ∀ s : ℝ, 0 < s → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        (∫ x : Fin n × Fin n → ℂ, matrixRegularizedLogDet (normalizedIidMatrix x) b s/(n : ℝ)
          ∂Measure.pi (fun _ => μ)) ≤ 2*Real.log b+s*M^2+ε := by
  obtain ⟨M, hM, hp⟩ := iid_regularizedLogDet_upper_probability μ c hc hexp hm hv b hb
  refine ⟨M, hM, ?_⟩
  intro s hs ε hε
  have h4 := squareExp_norm_pow_integrable μ c hc hexp 4
  let B := 2*(|Real.log s|+2*b^2+s)^2+8*(∫ z : ℂ, ‖z‖^4 ∂μ)
  apply eventually_integral_upper_of_probability (fun n => Fin n × Fin n → ℂ)
    (fun n => Measure.pi (fun _ : Fin n × Fin n => μ))
    (fun n x => matrixRegularizedLogDet (normalizedIidMatrix x) b s/(n : ℝ)) _ _ _
    (2*Real.log b+s*M^2) B _ _ _ (fun δ hδ => hp s hs.le δ hδ) ε hε
  · intro n
    exact ((matrixRegularizedLogDet_measurable n b s).comp
      (normalizedIidMatrix_continuous n).measurable).div_const _
  · exact Eventually.of_forall (fun n => (iidRegularizedLogDet_integrable μ c hc hexp n b s hs).div_const _)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact (iid_regularizedLogDet_secondMoment μ h4 n hn b s hs).1
  · have hl := Real.log_nonneg hb.le
    positivity
  · dsimp [B]
    have hi : 0 ≤ ∫ z : ℂ, ‖z‖^4 ∂μ := integral_nonneg (fun _ => by positivity)
    positivity
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact (iid_regularizedLogDet_secondMoment μ h4 n hn b s hs).2

#print axioms iid_regularizedLogDet_mean_upper
end SpectralRadiusUpperTail
