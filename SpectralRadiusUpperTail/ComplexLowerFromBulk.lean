import SpectralRadiusUpperTail.ComplexLikelihoodFromBulk
import SpectralRadiusUpperTail.ComplexLowerFromCost
import SpectralRadiusUpperTail.ComplexMatrixTiltException
import SpectralRadiusUpperTail.ProbabilityEventComparison

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology ENNReal

/-- The only analytic input retained here is the stated original-law, n²-scale bulk log-det bound. -/
lemma complex_spectral_log_lower_of_bulk
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℂ => Real.exp (4*c*‖x‖^2)) μ)
    (u ell κ δ b r : ℝ) (hu : 0 < u) (hell : 0 < ell) (hκ : 0 < κ) (hδ : 0 < δ)
    (hr : 1 < r) (hb : r < ‖((b : ℂ)/((u+1 : ℝ) : ℂ))‖)
    (C q : ℝ) (hC : 0 ≤ C) (hq : 0 < q)
    (hbulk : ∀ᶠ n : ℕ in atTop,
      (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        {x | regularizedResidualLogDet x (b : ℂ) (ell*u)/(n : ℝ) < 2*Real.log b-δ} ≤
          C*Real.exp (-q*(n : ℝ)^2)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, -lowerTiltCost 2 b u (ell+δ) κ (2*δ)-ε ≤
      Real.log ((Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        {x | r < (spectralRadius ℂ (normalizedArray x)).toReal})/(n : ℝ) := by
  obtain ⟨L,hL,hw⟩ := complex_likelihood_cost_on_bulk μ hm hvar hpseudo (4*c) (by positivity) hexp
    u ell κ δ b hu hell hκ hδ
  let ν : (n : ℕ) → Measure (flatUnitDirections ℂ n L) := fun n => haarFlatPrior ℂ n L hL
  letI : ∀ n, IsProbabilityMeasure (ν n) := fun n => haarFlatPrior_probability ℂ n L hL
  let E := fun n => {x : Fin n → Fin n → ℂ |
    regularizedResidualLogDet x (b : ℂ) (ell*u)/(n : ℝ) < 2*Real.log b-δ}
  have hE (n : ℕ) : MeasurableSet (E n) :=
    measurableSet_lt ((regularizedResidualLogDet_measurable n (b : ℂ) (ell*u)).div_const _) measurable_const
  have ht := complex_spectralTilt_quadratic_exception μ hm hvar hpseudo (4*c) (by positivity) hexp
    u hu L (by linarith) ν (b : ℂ) E hE C q hC hq hbulk
  letI : ∀ n, IsProbabilityMeasure (flatSpectralMatrixTilt μ (ν n) u (b : ℂ)) :=
    fun n => flatSpectralMatrixTilt_probability μ (ν n) u hu (b : ℂ)
  apply complex_spectral_log_lower_of_likelihood_cost μ hm hvar hpseudo c hc hexp
    u L hu hL ν (b : ℂ) r hr hb (lowerTiltCost 2 b u (ell+δ) κ (2*δ)) _ ε hε
  apply probability_tendsto_zero_of_eventual_subset (fun n => Fin n → Fin n → ℂ)
    (fun n => flatSpectralMatrixTilt μ (ν n) u (b : ℂ)) _ E _ ht
  filter_upwards [hw] with n hn
  intro x hx
  by_contra hnot
  have hg : 2*Real.log b-δ ≤ regularizedResidualLogDet x (b : ℂ) (ell*u)/(n : ℝ) :=
    le_of_not_gt hnot
  exact (not_lt_of_ge (hn x hg)) hx

#print axioms complex_spectral_log_lower_of_bulk
end SpectralRadiusUpperTail
