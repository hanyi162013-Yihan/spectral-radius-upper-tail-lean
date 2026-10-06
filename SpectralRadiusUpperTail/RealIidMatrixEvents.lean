import SpectralRadiusUpperTail.RealMatrixExteriorTransfer

namespace SpectralRadiusUpperTail
open MeasureTheory

lemma real_iid_matrix_event_le_complex {n : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (S : Matrix (Fin n) (Fin n) ℂ → Prop) :
    (Measure.pi (fun _ : Fin n × Fin n => μ)).real
      {x | S ((normalizedIidMatrix x).map Complex.ofRealHom)} ≤
    (Measure.pi (fun _ : Fin n × Fin n => complexifiedLaw μ)).real
      {x | S (normalizedIidMatrix x)} := by
  simp_rw [normalizedIidMatrix_complexify]
  rw [← iid_complexifiedLaw μ]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  have hf : Measurable (fun x : Fin n × Fin n → ℝ => fun i => (x i : ℂ)) := by
    apply measurable_pi_lambda
    intro i
    exact Complex.continuous_ofReal.measurable.comp (measurable_pi_apply i)
  exact Measure.le_map_apply hf.aemeasurable _

#print axioms real_iid_matrix_event_le_complex
end SpectralRadiusUpperTail
