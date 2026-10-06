import SpectralRadiusUpperTail.IidMatrixFlatten
import SpectralRadiusUpperTail.ActualMatrixIdentity
import SpectralRadiusUpperTail.MatrixMoments
import SpectralRadiusUpperTail.SpectralMeasurable

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- The flattened and nested iid Gaussian arrays give the same radius law. -/
theorem realGaussian_radius_event_eq_nested
    (n : ℕ) (S : Set ℝ) (hS : MeasurableSet S) :
    (gaussianMatrixLaw n).real
      {a | realMatrixRadius ((1/Real.sqrt (n : ℝ)) • entryMatrix a) ∈ S} =
    (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => standardNormal))).real
      {x | (spectralRadius ℂ ((normalizedArray x).map Complex.ofRealHom)).toReal ∈ S} := by
  let f := fun x : Fin n → Fin n → ℝ => fun ij : Fin n × Fin n => x ij.1 ij.2
  have hf : Measurable f := by fun_prop
  have hM : Measurable (fun a : Fin n × Fin n → ℝ =>
      realMatrixRadius ((1/Real.sqrt (n : ℝ)) • entryMatrix a)) :=
    realMatrixRadius_measurable.comp (scaled_entryMatrix_continuous _).measurable
  unfold Measure.real gaussianMatrixLaw
  rw [← iid_matrix_flatten_law standardNormal n]
  exact congrArg ENNReal.toReal (Measure.map_apply hf (hS.preimage hM))

theorem realGaussian_radius_strict_tail_eq_nested (n : ℕ) (r : ℝ) :
    (gaussianMatrixLaw n).real
      {a | r < realMatrixRadius ((1/Real.sqrt (n : ℝ)) • entryMatrix a)} =
    (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => standardNormal))).real
      {x | r < (spectralRadius ℂ ((normalizedArray x).map Complex.ofRealHom)).toReal} :=
  realGaussian_radius_event_eq_nested n (Set.Ioi r) measurableSet_Ioi

theorem realGaussian_radius_closed_tail_eq_nested (n : ℕ) (r : ℝ) :
    (gaussianMatrixLaw n).real
      {a | r ≤ realMatrixRadius ((1/Real.sqrt (n : ℝ)) • entryMatrix a)} =
    (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => standardNormal))).real
      {x | r ≤ (spectralRadius ℂ ((normalizedArray x).map Complex.ofRealHom)).toReal} :=
  realGaussian_radius_event_eq_nested n (Set.Ici r) measurableSet_Ici

#print axioms realGaussian_radius_event_eq_nested
#print axioms realGaussian_radius_strict_tail_eq_nested
#print axioms realGaussian_radius_closed_tail_eq_nested
end SpectralRadiusUpperTail
