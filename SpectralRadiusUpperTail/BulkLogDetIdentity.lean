import SpectralRadiusUpperTail.IidRegularizedLogDetIntegrable
import SpectralRadiusUpperTail.IidMatrixFlatten
import SpectralRadiusUpperTail.SphereResidualWeight

namespace SpectralRadiusUpperTail
open MeasureTheory

lemma normalizedIidMatrix_flatten_eq {𝕂 : Type*} [RCLike 𝕂] {n : ℕ}
    (x : Fin n → Fin n → 𝕂) :
    normalizedIidMatrix (fun ij : Fin n × Fin n => x ij.1 ij.2) = normalizedArray x := by
  ext i j
  simp only [normalizedIidMatrix, normalizedArray, Matrix.smul_apply, Matrix.of_apply,
    smul_eq_mul, RCLike.real_smul_eq_coe_mul]

lemma regularizedResidualLogDet_eq_matrix {n : ℕ} (x : Fin n → Fin n → ℂ) (b s : ℝ) :
    regularizedResidualLogDet x (b : ℂ) s = matrixRegularizedLogDet (normalizedArray x) b s := rfl

lemma iid_regularizedResidualLogDet_integral (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (n : ℕ) (b s : ℝ) :
    (∫ x : Fin n → Fin n → ℂ, regularizedResidualLogDet x (b : ℂ) s/(n : ℝ)
      ∂Measure.pi (fun _ => Measure.pi (fun _ => μ))) =
    ∫ x : Fin n × Fin n → ℂ, matrixRegularizedLogDet (normalizedIidMatrix x) b s/(n : ℝ)
      ∂Measure.pi (fun _ => μ) := by
  have hm : Measurable (fun x : Fin n × Fin n → ℂ =>
      matrixRegularizedLogDet (normalizedIidMatrix x) b s/(n : ℝ)) :=
    ((matrixRegularizedLogDet_measurable n b s).comp
      (normalizedIidMatrix_continuous n).measurable).div_const _
  rw [← iid_matrix_flatten_law μ n, integral_map
    (show Measurable (fun x : Fin n → Fin n → ℂ => fun ij : Fin n × Fin n => x ij.1 ij.2) by fun_prop).aemeasurable
    hm.aestronglyMeasurable]
  simp only [normalizedIidMatrix_flatten_eq, regularizedResidualLogDet_eq_matrix]

lemma iid_regularizedResidualLogDet_probability (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (n : ℕ) (b s a : ℝ) :
    (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
      {x | regularizedResidualLogDet x (b : ℂ) s/(n : ℝ) < a} =
    (Measure.pi (fun _ : Fin n × Fin n => μ)).real
      {x | matrixRegularizedLogDet (normalizedIidMatrix x) b s/(n : ℝ) < a} := by
  rw [← iid_matrix_flatten_law μ n]
  have hm : Measurable (fun x : Fin n × Fin n → ℂ =>
      matrixRegularizedLogDet (normalizedIidMatrix x) b s/(n : ℝ)) :=
    ((matrixRegularizedLogDet_measurable n b s).comp
      (normalizedIidMatrix_continuous n).measurable).div_const _
  unfold Measure.real
  rw [Measure.map_apply (by fun_prop) (measurableSet_lt hm measurable_const)]
  congr 1

#print axioms normalizedIidMatrix_flatten_eq
#print axioms regularizedResidualLogDet_eq_matrix
#print axioms iid_regularizedResidualLogDet_integral
#print axioms iid_regularizedResidualLogDet_probability
end SpectralRadiusUpperTail
