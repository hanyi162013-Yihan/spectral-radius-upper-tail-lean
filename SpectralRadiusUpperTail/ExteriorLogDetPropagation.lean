import SpectralRadiusUpperTail.ExteriorLogDetDerivative
import SpectralRadiusUpperTail.TraceGoodEvent
import Mathlib.Analysis.Calculus.MeanValue

namespace SpectralRadiusUpperTail
open Set

lemma exteriorLogDet_propagation {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (r b B ε : ℝ) (hr : 0 < r) (hrb : r ≤ b) (hbB : b ≤ B)
    (htrace : matrixTraceControl A r ε) :
    |normalizedExteriorLogDet A b-Real.log b| ≤
      |normalizedExteriorLogDet A B-Real.log B|+ε*(B-b) := by
  let f : ℝ → ℝ := fun t => normalizedExteriorLogDet A t-Real.log t
  let d : ℝ → ℝ := fun t => (normalizedMatrixTrace (resolvent A (t : ℂ))).re-t⁻¹
  have ht (t : ℝ) (ht : t ∈ Icc b B) : r ≤ ‖(t : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr.trans_le (hrb.trans ht.1))]
    exact hrb.trans ht.1
  have hd : ∀ t ∈ Icc b B, HasDerivWithinAt f (d t) (Icc b B) t := by
    intro t hti
    exact ((normalizedExteriorLogDet_hasDerivAt A t (htrace t (ht t hti)).1).sub
      (Real.hasDerivAt_log (ne_of_gt (hr.trans_le (hrb.trans hti.1))))).hasDerivWithinAt
  have hbound : ∀ t ∈ Ico b B, ‖d t‖ ≤ ε := by
    intro t hti
    have hh := (htrace t (ht t ⟨hti.1, hti.2.le⟩)).2
    have he : d t = (normalizedMatrixTrace (resolvent A (t : ℂ))-(t : ℂ)⁻¹).re := by
      simp [d]
    rw [he, Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans hh.le
  have hh := norm_image_sub_le_of_norm_deriv_le_segment' hd hbound B ⟨hbB, le_rfl⟩
  change |f b| ≤ |f B|+ε*(B-b)
  have ht := abs_sub_le (f b) (f B) 0
  simp only [sub_zero] at ht
  have he : |f b-f B| ≤ ε*(B-b) := by
    rw [abs_sub_comm]
    exact hh
  linarith

#print axioms exteriorLogDet_propagation
end SpectralRadiusUpperTail
