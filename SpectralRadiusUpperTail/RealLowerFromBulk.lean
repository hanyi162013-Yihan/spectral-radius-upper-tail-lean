import SpectralRadiusUpperTail.RealLikelihoodFromBulk
import SpectralRadiusUpperTail.RealLowerFromCost
import SpectralRadiusUpperTail.RealMatrixTiltException
import SpectralRadiusUpperTail.ProbabilityEventComparison

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology ENNReal

/-- The only analytic input retained here is the stated original-law, n²-scale bulk log-det bound. -/
lemma real_spectral_log_lower_of_bulk
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hvar : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℝ => Real.exp (4*c*‖x‖^2)) μ)
    (u ell κ δ b r : ℝ) (hu : 0 < u) (hell : 0 < ell) (hκ : 0 < κ) (hδ : 0 < δ)
    (hr : 1 < r) (hb : r < ‖((b/(u+1) : ℝ) : ℂ)‖)
    (C q : ℝ) (hC : 0 ≤ C) (hq : 0 < q)
    (hbulk : ∀ᶠ n : ℕ in atTop,
      (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        {x | regularizedResidualLogDet x (b : ℝ) (ell*u)/(n : ℝ) < 2*Real.log b-δ} ≤
          C*Real.exp (-q*(n : ℝ)^2)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, -lowerTiltCost 1 b u (ell+δ) κ (2*δ)-ε ≤
      Real.log ((Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        {x | r < (spectralRadius ℂ ((normalizedArray x).map Complex.ofRealHom)).toReal})/(n : ℝ) := by
  obtain ⟨L,hL,hw⟩ := real_likelihood_cost_on_bulk μ hm hvar (4*c) (by positivity) hexp
    u ell κ δ b hu hell hκ hδ
  let ν : (n : ℕ) → Measure (flatUnitDirections ℝ n L) := fun n => haarFlatPrior ℝ n L hL
  letI : ∀ n, IsProbabilityMeasure (ν n) := fun n => haarFlatPrior_probability ℝ n L hL
  let E := fun n => {x : Fin n → Fin n → ℝ |
    regularizedResidualLogDet x (b : ℝ) (ell*u)/(n : ℝ) < 2*Real.log b-δ}
  have hE (n : ℕ) : MeasurableSet (E n) :=
    measurableSet_lt ((regularizedResidualLogDet_measurable n (b : ℝ) (ell*u)).div_const _) measurable_const
  have ht := real_spectralTilt_quadratic_exception μ hm hvar (4*c) (by positivity) hexp
    (2*u) (by positivity) L (by linarith) ν (b : ℝ) E hE C q hC hq hbulk
  letI : ∀ n, IsProbabilityMeasure (flatSpectralMatrixTilt μ (ν n) (2*u) (b : ℝ)) :=
    fun n => flatSpectralMatrixTilt_probability μ (ν n) (2*u) (by positivity) (b : ℝ)
  apply real_spectral_log_lower_of_likelihood_cost μ hm hvar c hc hexp
    u L hu hL ν (b : ℝ) r hr hb (lowerTiltCost 1 b u (ell+δ) κ (2*δ)) _ ε hε
  apply probability_tendsto_zero_of_eventual_subset (fun n => Fin n → Fin n → ℝ)
    (fun n => flatSpectralMatrixTilt μ (ν n) (2*u) (b : ℝ)) _ E _ ht
  filter_upwards [hw] with n hn
  intro x hx
  by_contra hnot
  have hg : 2*Real.log b-δ ≤ regularizedResidualLogDet x (b : ℝ) (ell*u)/(n : ℝ) :=
    le_of_not_gt hnot
  exact (not_lt_of_ge (hn x hg)) hx

#print axioms real_spectral_log_lower_of_bulk
end SpectralRadiusUpperTail
