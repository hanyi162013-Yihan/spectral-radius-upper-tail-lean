import SpectralRadiusUpperTail.OutlierEventMeasurable

namespace SpectralRadiusUpperTail
open Metric
open scoped Matrix

lemma real_closedBall_complex_iff (z b d : ℝ) :
    (z : ℂ) ∈ closedBall (b : ℂ) d ↔ z ∈ closedBall b d := by
  simp only [mem_closedBall,dist_eq_norm,← Complex.ofReal_sub,Complex.norm_real]

lemma isClosed_matrix_real_outlier_event (n : ℕ) (b d : ℝ) :
    IsClosed {A : Matrix (Fin n) (Fin n) ℂ | ∃ z : ℝ,
      (z : ℂ) ∈ closedBall (b : ℂ) d ∧ (z : ℂ) ∈ spectrum ℂ A} := by
  let K := closedBall b d
  letI : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall b d)
  have hc : Continuous (fun x : K × Matrix (Fin n) (Fin n) ℂ =>
      ((x.1.val : ℂ)) • (1 : Matrix (Fin n) (Fin n) ℂ)-x.2) := by
    fun_prop
  have hh := isClosedMap_snd_of_compactSpace
    {x : K × Matrix (Fin n) (Fin n) ℂ |
      (((x.1.val : ℂ)) • (1 : Matrix (Fin n) (Fin n) ℂ)-x.2).det = 0}
    (isClosed_eq hc.matrix_det continuous_const)
  convert hh using 1
  ext A
  simp only [Set.mem_setOf_eq,Set.mem_image,Prod.exists,exists_eq_right]
  constructor
  · rintro ⟨z,hz,he⟩
    exact ⟨⟨z,(real_closedBall_complex_iff z b d).1 hz⟩,
      (matrix_mem_spectrum_iff_det_zero A z).1 he⟩
  · rintro ⟨z,hz⟩
    exact ⟨z.val,(real_closedBall_complex_iff z.val b d).2 z.property,
      (matrix_mem_spectrum_iff_det_zero A z.val).2 hz⟩

lemma measurableSet_matrix_real_outlier_event (n : ℕ) (b d : ℝ) :
    MeasurableSet {A : Matrix (Fin n) (Fin n) ℂ | ∃ z : ℝ,
      (z : ℂ) ∈ closedBall (b : ℂ) d ∧ (z : ℂ) ∈ spectrum ℂ A} :=
  (isClosed_matrix_real_outlier_event n b d).measurableSet

#print axioms real_closedBall_complex_iff
#print axioms isClosed_matrix_real_outlier_event
#print axioms measurableSet_matrix_real_outlier_event
end SpectralRadiusUpperTail
