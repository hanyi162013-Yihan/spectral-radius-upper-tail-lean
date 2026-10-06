import SpectralRadiusUpperTail.IidUniformExteriorLogDet
import SpectralRadiusUpperTail.RealMatrixExteriorTransfer

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

lemma iid_real_uniform_exteriorLogDet_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℝ => Real.exp (c*‖x‖^2)) μ)
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hv : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (r R ε : ℝ) (hr : 1 < r) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n × Fin n => μ)).real
      {x | ¬ ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ R →
        |normalizedComplexLogDet ((normalizedIidMatrix x).map Complex.ofRealHom) z-Real.log ‖z‖| < ε})
      atTop (𝓝 0) := by
  have hlim := iid_uniform_exteriorLogDet_probability (complexifiedLaw μ) c hc
    (complexifiedLaw_squareExp μ c hexp)
    (by rw [complexifiedLaw_mean, hm]; rfl)
    (by rw [complexifiedLaw_energy, hv]) r R ε hr hε
  apply squeeze_zero (fun _ => measureReal_nonneg) _ hlim
  intro n
  simp_rw [normalizedIidMatrix_complexify]
  rw [← iid_complexifiedLaw μ]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  have hf : Measurable (fun x : Fin n × Fin n → ℝ => fun i => (x i : ℂ)) := by
    apply measurable_pi_lambda
    intro i
    exact Complex.continuous_ofReal.measurable.comp (measurable_pi_apply i)
  exact Measure.le_map_apply hf.aemeasurable _

#print axioms iid_real_uniform_exteriorLogDet_probability
end SpectralRadiusUpperTail
