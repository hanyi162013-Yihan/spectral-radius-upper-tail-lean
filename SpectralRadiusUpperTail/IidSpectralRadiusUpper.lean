import SpectralRadiusUpperTail.IidExteriorResolvent
import SpectralRadiusUpperTail.ExteriorSpectralRadius

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

lemma iid_complex_spectralRadius_upper (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (r : ℝ) (hr : 1 < r) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n × Fin n => μ)).real
      {x | r ≤ (spectralRadius ℂ (normalizedIidMatrix x)).toReal}) atTop (𝓝 0) := by
  let s := (1+r)/2
  have hs : 1 < s := by dsimp [s]; linarith
  have hsr : s < r := by dsimp [s]; linarith
  obtain ⟨C,hC,hlim⟩ := iid_exterior_resolvent_probability μ c hc hexp hm hv s hs
  apply squeeze_zero (fun _ => measureReal_nonneg) _ hlim
  intro n
  apply measureReal_mono (μ := Measure.pi (fun _ : Fin n × Fin n => μ))
  intro x hx hgood
  have hh := matrixExteriorControl_radius_le (normalizedIidMatrix x) s C
    (lt_trans (by norm_num) hs).le hgood
  exact (not_le_of_gt hsr) (hx.trans hh)

#print axioms iid_complex_spectralRadius_upper
end SpectralRadiusUpperTail
