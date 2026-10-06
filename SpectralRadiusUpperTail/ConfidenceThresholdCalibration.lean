import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace SpectralRadiusUpperTail

/-- Deterministic calibration of the square-root and linear confidence terms.
The assumptions describe the variance and increment envelopes, not a target tail bound. -/
lemma confidence_threshold_calibration {V b x y D C r : ℝ}
    (hy : 0 < y) (hD : 0 ≤ D) (hC : 0 ≤ C) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hV : V*y ≤ D*x) (hb : b*y ≤ 2*C*x) (he : r^2*y = x^3) :
    4*Real.sqrt (V*(2*x^2))+8*b*(2*x^2) ≤ (4*Real.sqrt (2*D)+32*C)*r := by
  have hsq : V*(2*x^2) ≤ (2*D)*r^2 := by
    apply (mul_le_mul_iff_left₀ hy).mp
    calc
      _ = (V*y)*(2*x^2) := by ring
      _ ≤ (D*x)*(2*x^2) := mul_le_mul_of_nonneg_right hV (by positivity)
      _ = ((2*D)*r^2)*y := by rw [show ((2*D)*r^2)*y = (2*D)*(r^2*y) by ring, he]; ring
  have hs : Real.sqrt (V*(2*x^2)) ≤ Real.sqrt (2*D)*r := by
    apply (Real.sqrt_le_iff).2
    refine ⟨mul_nonneg (Real.sqrt_nonneg _) hr, ?_⟩
    rw [mul_pow, Real.sq_sqrt (mul_nonneg (by norm_num) hD)]
    exact hsq
  have hlin : 8*b*(2*x^2) ≤ 32*C*r^2 := by
    apply (mul_le_mul_iff_left₀ hy).mp
    calc
      _ = (b*y)*(16*x^2) := by ring
      _ ≤ (2*C*x)*(16*x^2) := mul_le_mul_of_nonneg_right hb (by positivity)
      _ = (32*C*r^2)*y := by rw [show (32*C*r^2)*y = (32*C)*(r^2*y) by ring, he]; ring
  have hr2 : r^2 ≤ r := by nlinarith
  have hc := mul_le_mul_of_nonneg_left hr2 (mul_nonneg (show (0 : ℝ) ≤ 32 by norm_num) hC)
  nlinarith

#print axioms confidence_threshold_calibration
end SpectralRadiusUpperTail
