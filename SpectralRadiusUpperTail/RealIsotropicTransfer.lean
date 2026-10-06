import SpectralRadiusUpperTail.IidIsotropicResolvent
import SpectralRadiusUpperTail.RealMatrixExteriorTransfer

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology BigOperators

lemma real_isotropic_failure_le_complex {n : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (p q : Fin n → ℂ) (r ε : ℝ) :
    (Measure.pi (fun _ : Fin n × Fin n => μ)).real
      {x | ¬ matrixIsotropicControl ((normalizedIidMatrix x).map Complex.ofRealHom) p q r ε} ≤
    (Measure.pi (fun _ : Fin n × Fin n => complexifiedLaw μ)).real
      {x | ¬ matrixIsotropicControl (normalizedIidMatrix x) p q r ε} := by
  simp_rw [normalizedIidMatrix_complexify]
  rw [← iid_complexifiedLaw μ]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  have hf : Measurable (fun x : Fin n × Fin n → ℝ => fun i => (x i : ℂ)) := by
    apply measurable_pi_lambda
    intro i
    exact Complex.continuous_ofReal.measurable.comp (measurable_pi_apply i)
  exact Measure.le_map_apply hf.aemeasurable _

lemma iid_real_isotropic_resolvent_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℝ => Real.exp (c*‖x‖^2)) μ)
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hv : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (p q : (n : ℕ) → Fin n → ℂ)
    (hp : ∀ n, (∑ i, ‖p n i‖^2) ≤ 1) (hq : ∀ n, (∑ i, ‖q n i‖^2) ≤ 1)
    (r ε : ℝ) (hr : 1 < r) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n × Fin n => μ)).real
      {x | ¬ matrixIsotropicControl ((normalizedIidMatrix x).map Complex.ofRealHom)
        (p n) (q n) r ε}) atTop (𝓝 0) := by
  have hh := iid_isotropic_resolvent_probability (complexifiedLaw μ) c hc
    (complexifiedLaw_squareExp μ c hexp)
    (by rw [complexifiedLaw_mean,hm]; rfl)
    (by rw [complexifiedLaw_energy,hv]) p q hp hq r ε hr hε
  exact squeeze_zero (fun _ => measureReal_nonneg)
    (fun n => real_isotropic_failure_le_complex μ (p n) (q n) r ε) hh

#print axioms real_isotropic_failure_le_complex
#print axioms iid_real_isotropic_resolvent_probability
end SpectralRadiusUpperTail
