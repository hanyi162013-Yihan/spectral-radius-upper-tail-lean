import SpectralRadiusUpperTail.ComplexLowerFromBulk
import SpectralRadiusUpperTail.MatchingParameterChoice

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- Matching lower rate, conditional only on the explicit quadratic-speed bulk estimate. -/
lemma complex_matching_lower_of_bulk
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℂ => Real.exp (4*c*‖x‖^2)) μ)
    (r : ℝ) (hr : 1 < r)
    (hbulk : ∀ b : ℝ, r < b → ∀ s : ℝ, 0 < s →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ q : ℝ, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
        (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
          {x | regularizedResidualLogDet x (b : ℂ) (s*s)/(n : ℝ) < 2*Real.log b-s} ≤
            C*Real.exp (-q*(n : ℝ)^2)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, -rate 2 r-ε ≤
      Real.log ((Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        {x | r < (spectralRadius ℂ (normalizedArray x)).toReal})/(n : ℝ) := by
  obtain ⟨b,hbr,s,hs,hcenter,hcost⟩ := matching_tilt_parameters 2 r (ε/2) hr (by positivity)
  obtain ⟨C,hC,q,hq,hbad⟩ := hbulk b hbr s hs
  have hbpos : 0 < b := by linarith
  have hnorm : r < ‖((b : ℂ)/((s+1 : ℝ) : ℂ))‖ := by
    rw [norm_div,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_pos hbpos,abs_of_pos (by positivity : 0 < s+1)]
    simpa only [add_comm] using hcenter
  have ht := complex_spectral_log_lower_of_bulk μ hm hvar hpseudo c hc hexp
    s s s s b r hs hs hs hs hr hnorm C q hC hq hbad (ε/2) (by positivity)
  filter_upwards [ht] with n hn
  rw [show s+s = 2*s by ring] at hn
  linarith

#print axioms complex_matching_lower_of_bulk
end SpectralRadiusUpperTail
