import SpectralRadiusUpperTail.IidComplexRegularizedSecondMoment
import SpectralRadiusUpperTail.IidUniformRegularizedLogDetUpper
import SpectralRadiusUpperTail.UniformUpperMeanLimit

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

lemma iid_uniform_regularizedLogDet_mean_upper (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (r : ℝ) (hr : 1 < r) :
    ∃ M : ℝ, 0 < M ∧ ∀ R s : ℝ, 0 < s → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ R →
        (∫ x : Fin n × Fin n → ℂ, complexRegularizedLogDet (normalizedIidMatrix x) z s/(n : ℝ)
          ∂Measure.pi (fun _ => μ)) ≤ 2*Real.log ‖z‖+s*M^2+ε := by
  obtain ⟨M, hM, hp⟩ := iid_uniform_regularizedLogDet_upper_probability μ c hc hexp hm hv r hr
  refine ⟨M, hM, ?_⟩
  intro R s hs ε hε
  let S := {z : ℂ // r ≤ ‖z‖ ∧ ‖z‖ ≤ R}
  let a : S → ℝ := fun z => 2*Real.log ‖z.val‖+s*M^2
  let F := fun n (z : S) (x : Fin n × Fin n → ℂ) =>
    complexRegularizedLogDet (normalizedIidMatrix x) z.val s/(n : ℝ)
  let B := 2*(|Real.log s|+2*R^2+s)^2+8*(∫ z : ℂ, ‖z‖^4 ∂μ)
  have h4 := squareExp_norm_pow_integrable μ c hc hexp 4
  have hprob (δ : ℝ) (hδ : 0 < δ) : Tendsto
      (fun n => (Measure.pi (fun _ : Fin n × Fin n => μ)).real {x | ∃ z : S, a z+δ < F n z x})
      atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => measureReal_nonneg) _ (hp R s hs.le δ hδ)
    intro n
    apply measureReal_mono (μ := Measure.pi (fun _ : Fin n × Fin n => μ))
    intro x hx hgood
    obtain ⟨z, hz⟩ := hx
    exact (not_lt_of_ge (hgood z.val z.property.1 z.property.2)) hz
  have hmean : ∀ᶠ n in atTop, ∀ z : S,
      (∫ x : Fin n × Fin n → ℂ, F n z x ∂Measure.pi (fun _ => μ)) ≤ a z+ε := by
    apply eventually_uniform_integral_upper_of_probability (fun n => Fin n × Fin n → ℂ)
      (fun n => Measure.pi (fun _ : Fin n × Fin n => μ)) S F _ _ _ a B _ _ _ hprob ε hε
    · intro n z
      exact ((complexRegularizedLogDet_measurable n z.val s).comp
        (normalizedIidMatrix_continuous n).measurable).div_const _
    · filter_upwards [eventually_gt_atTop 0] with n hn z
      exact iid_complexRegularizedLogDet_integrable μ h4 n hn z.val s hs
    · filter_upwards [eventually_gt_atTop 0] with n hn z
      exact (iid_complexRegularizedLogDet_secondMoment μ h4 n hn z.val s R hs z.property.2).1
    · intro z
      have hl := Real.log_nonneg (hr.le.trans z.property.1)
      dsimp [a]
      positivity
    · dsimp [B]
      have hi : 0 ≤ ∫ z : ℂ, ‖z‖^4 ∂μ := integral_nonneg (fun _ => by positivity)
      positivity
    · filter_upwards [eventually_gt_atTop 0] with n hn z
      exact (iid_complexRegularizedLogDet_secondMoment μ h4 n hn z.val s R hs z.property.2).2
  filter_upwards [hmean] with n hn z hrz hzR
  exact hn ⟨z, hrz, hzR⟩

#print axioms iid_uniform_regularizedLogDet_mean_upper
end SpectralRadiusUpperTail
