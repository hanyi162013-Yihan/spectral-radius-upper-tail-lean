import SpectralRadiusUpperTail.OutlierEventMeasurable

namespace SpectralRadiusUpperTail
open Metric
open scoped Matrix.Norms.Frobenius ENNReal NNReal

lemma complex_eigenvalue_le_spectralRadius {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (z : ℂ) (hz : z ∈ spectrum ℂ A) : ‖z‖ ≤ (spectralRadius ℂ A).toReal := by
  have hb : (spectralRadius ℂ A) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (complex_spectralRadius_le_frobenius A)
  have hh : (‖z‖₊ : ℝ≥0∞) ≤ spectralRadius ℂ A := le_iSup_of_le z (le_iSup_of_le hz le_rfl)
  simpa only [ENNReal.coe_toReal,coe_nnnorm] using ENNReal.toReal_mono hb hh

lemma spectralRadius_gt_of_outlier {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (b : ℂ) (d r : ℝ) (hr : r < ‖b‖-d)
    (h : ∃ z ∈ closedBall b d, z ∈ spectrum ℂ A) :
    r < (spectralRadius ℂ A).toReal := by
  obtain ⟨z,hz,hs⟩ := h
  have hd : ‖z-b‖ ≤ d := by simpa only [mem_closedBall,dist_eq_norm] using hz
  have hn : ‖b‖ ≤ ‖z‖+d := by
    have hh := norm_sub_le z (z-b)
    simp only [sub_sub_cancel] at hh
    linarith
  have he := complex_eigenvalue_le_spectralRadius A z hs
  linarith

lemma outlier_disk_above_radius (b : ℂ) (r : ℝ) (hr : 1 < r) (hb : r < ‖b‖) :
    ∃ d : ℝ, 0 < d ∧ 3*d < ‖b‖-1 ∧ r < ‖b‖-d := by
  refine ⟨min (‖b‖-1) (‖b‖-r)/4,?_,?_,?_⟩
  · exact div_pos (lt_min (by linarith) (by linarith)) (by norm_num)
  · have h := min_le_left (‖b‖-1) (‖b‖-r)
    linarith
  · have h := min_le_right (‖b‖-1) (‖b‖-r)
    linarith

#print axioms complex_eigenvalue_le_spectralRadius
#print axioms spectralRadius_gt_of_outlier
#print axioms outlier_disk_above_radius
end SpectralRadiusUpperTail
