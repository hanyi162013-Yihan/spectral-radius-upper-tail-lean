import SpectralRadiusUpperTail.IidExteriorResolvent
import SpectralRadiusUpperTail.RealMatrixExteriorTransfer
import SpectralRadiusUpperTail.ExteriorSpectralRadius
import SpectralRadiusUpperTail.SpectralWitness

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

lemma iid_real_exterior_resolvent_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℝ => Real.exp (c*‖x‖^2)) μ)
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hv : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (r : ℝ) (hr : 1 < r) :
    ∃ C : ℝ, 0 < C ∧ Tendsto (fun n : ℕ =>
      (Measure.pi (fun _ : Fin n × Fin n => μ)).real
        {x | ¬ matrixExteriorControl ((normalizedIidMatrix x).map Complex.ofRealHom) r C})
      atTop (𝓝 0) := by
  obtain ⟨C,hC,hlim⟩ := iid_exterior_resolvent_probability (complexifiedLaw μ) c hc
    (complexifiedLaw_squareExp μ c hexp)
    (by rw [complexifiedLaw_mean,hm]; rfl)
    (by rw [complexifiedLaw_energy,hv]) r hr
  exact ⟨C,hC,squeeze_zero (fun _ => measureReal_nonneg)
    (fun _ => real_exterior_failure_le_complex μ r C) hlim⟩

lemma iid_real_spectralRadius_upper (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℝ => Real.exp (c*‖x‖^2)) μ)
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hv : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (r : ℝ) (hr : 1 < r) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n × Fin n => μ)).real
      {x | r ≤ realMatrixRadius (normalizedIidMatrix x)}) atTop (𝓝 0) := by
  let s := (1+r)/2
  have hs : 1 < s := by dsimp [s]; linarith
  have hsr : s < r := by dsimp [s]; linarith
  obtain ⟨C,hC,hlim⟩ := iid_real_exterior_resolvent_probability μ c hc hexp hm hv s hs
  apply squeeze_zero (fun _ => measureReal_nonneg) _ hlim
  intro n
  apply measureReal_mono (μ := Measure.pi (fun _ : Fin n × Fin n => μ))
  intro x hx hgood
  have hh := matrixExteriorControl_radius_le ((normalizedIidMatrix x).map Complex.ofRealHom) s C
    (lt_trans (by norm_num) hs).le hgood
  exact (not_le_of_gt hsr) (hx.trans hh)

#print axioms iid_real_exterior_resolvent_probability
#print axioms iid_real_spectralRadius_upper
end SpectralRadiusUpperTail
