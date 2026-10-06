import SpectralRadiusUpperTail.SpectralMeasurable
import SpectralRadiusUpperTail.OutlierProbability
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Algebra.Group.Matrix

namespace SpectralRadiusUpperTail
open Metric
open scoped Matrix

lemma matrix_mem_spectrum_iff_det_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    z ∈ spectrum ℂ A ↔ (z • (1 : Matrix (Fin n) (Fin n) ℂ)-A).det = 0 := by
  rw [spectrum.mem_iff,Matrix.isUnit_iff_isUnit_det]
  simp only [isUnit_iff_ne_zero,not_not,Algebra.algebraMap_eq_smul_one]

lemma isClosed_matrix_outlier_event (n : ℕ) (b : ℂ) (d : ℝ) :
    IsClosed {A : Matrix (Fin n) (Fin n) ℂ | ∃ z ∈ closedBall b d, z ∈ spectrum ℂ A} := by
  let K := closedBall b d
  letI : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall b d)
  have hc : Continuous (fun x : K × Matrix (Fin n) (Fin n) ℂ =>
      ((x.1.val) • (1 : Matrix (Fin n) (Fin n) ℂ)-x.2).det) := by
    fun_prop
  have hh := isClosedMap_snd_of_compactSpace
    {x : K × Matrix (Fin n) (Fin n) ℂ |
      ((x.1.val) • (1 : Matrix (Fin n) (Fin n) ℂ)-x.2).det = 0}
    (isClosed_eq hc continuous_const)
  convert hh using 1
  ext A
  simp only [Set.mem_setOf_eq,Set.mem_image,Prod.exists,exists_eq_right]
  constructor
  · rintro ⟨z,hz,he⟩
    exact ⟨⟨z,hz⟩,(matrix_mem_spectrum_iff_det_zero A z).1 he⟩
  · rintro ⟨z,hz⟩
    exact ⟨z.val,z.property,(matrix_mem_spectrum_iff_det_zero A z.val).2 hz⟩

lemma measurableSet_matrix_outlier_event (n : ℕ) (b : ℂ) (d : ℝ) :
    MeasurableSet {A : Matrix (Fin n) (Fin n) ℂ | ∃ z ∈ closedBall b d, z ∈ spectrum ℂ A} :=
  (isClosed_matrix_outlier_event n b d).measurableSet

#print axioms matrix_mem_spectrum_iff_det_zero
#print axioms isClosed_matrix_outlier_event
#print axioms measurableSet_matrix_outlier_event
end SpectralRadiusUpperTail
