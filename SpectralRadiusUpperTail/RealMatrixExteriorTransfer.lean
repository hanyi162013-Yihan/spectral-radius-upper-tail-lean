import SpectralRadiusUpperTail.IidNormalizedGramMoment
import SpectralRadiusUpperTail.RealComplexIidLaw
import SpectralRadiusUpperTail.MatrixExteriorPowerBound

namespace SpectralRadiusUpperTail
open MeasureTheory

lemma normalizedIidMatrix_complexify {n : ℕ} (x : Fin n × Fin n → ℝ) :
    (normalizedIidMatrix x).map Complex.ofRealHom =
      normalizedIidMatrix (fun i => (x i : ℂ)) := by
  ext i j
  simp only [normalizedIidMatrix, Matrix.map_apply, Matrix.smul_apply, Matrix.of_apply,
    smul_eq_mul, Complex.ofRealHom_eq_coe, Complex.ofReal_mul, RCLike.ofReal_real_eq_id, id_eq]
  rfl

lemma real_exterior_failure_le_complex {n : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (r C : ℝ) :
    (Measure.pi (fun _ : Fin n × Fin n => μ)).real
      {x | ¬ matrixExteriorControl ((normalizedIidMatrix x).map Complex.ofRealHom) r C} ≤
    (Measure.pi (fun _ : Fin n × Fin n => complexifiedLaw μ)).real
      {x | ¬ matrixExteriorControl (normalizedIidMatrix x) r C} := by
  simp_rw [normalizedIidMatrix_complexify]
  rw [← iid_complexifiedLaw μ]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  have hf : Measurable (fun x : Fin n × Fin n → ℝ => fun i => (x i : ℂ)) := by
    apply measurable_pi_lambda
    intro i
    exact Complex.continuous_ofReal.measurable.comp (measurable_pi_apply i)
  exact Measure.le_map_apply hf.aemeasurable _

#print axioms normalizedIidMatrix_complexify
#print axioms real_exterior_failure_le_complex
end SpectralRadiusUpperTail
