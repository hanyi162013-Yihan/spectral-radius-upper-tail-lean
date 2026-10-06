import SpectralRadiusUpperTail.ConfidenceThresholdCalibration

namespace SpectralRadiusUpperTail

lemma affine_confidence_calibration (c A B L x y r : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hL : 0 ≤ L) (hx : 1 ≤ x)
    (hy : 0 < y) (hr : 0 ≤ r) (hr1 : r ≤ 1) (he : r^2*y = x^3) :
    4*Real.sqrt ((c*(A*x+2)*(L/y))*(2*x^2)) +
      8*(2*(B*x+1)/y)*(2*x^2) ≤
      (4*Real.sqrt (2*(|c| *(A+2)*L))+32*(B+1))*r := by
  apply confidence_threshold_calibration hy
    (mul_nonneg (mul_nonneg (abs_nonneg c) (by linarith)) hL)
    (by linarith) hr hr1
  · have hx0 : 0 ≤ x := by linarith
    calc
      (c*(A*x+2)*(L/y))*y = c*(A*x+2)*L := by field_simp
      _ ≤ |c| *(A*x+2)*L :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)) hL
      _ ≤ |c| *((A+2)*x)*L := by
        apply mul_le_mul_of_nonneg_right _ hL
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
        nlinarith
      _ = (|c| *(A+2)*L)*x := by ring
  · calc
      (2*(B*x+1)/y)*y = 2*(B*x+1) := div_mul_cancel₀ _ hy.ne'
      _ ≤ 2*(B+1)*x := by nlinarith
  · exact he

#print axioms affine_confidence_calibration
end SpectralRadiusUpperTail
