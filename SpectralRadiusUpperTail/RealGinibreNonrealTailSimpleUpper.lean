import SpectralRadiusUpperTail.RealGinibreNonrealTailUpper
import SpectralRadiusUpperTail.ComplexUnitBallVolume
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set Metric

/-- The planar nonreal one-point mass has a constant prefactor and the
strictly faster `-I₂(r)` exponential rate. -/
theorem realGinibreNonrealTailSimpleUpper (n : ℕ) (r : ℝ)
    (hr : 1 < r) (hnpos : 0 < n)
    (hn : 1/r ≤ (n : ℝ)*(r-1/r)) :
    (∫ z : ℂ in {z | r < ‖z‖}, realGinibreNonrealDensityAt n z) ≤
      (2*r/(r-1/r)) * Real.exp (-(n : ℝ)*rate 2 r) := by
  have hrpos : 0 < r := by linarith
  have hc : 0 < r-1/r := by
    have hsq : 1 < r^2 := by nlinarith
    apply sub_pos.mpr
    apply (div_lt_iff₀ hrpos).mpr
    nlinarith
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
  have h := realGinibreNonrealTailUpper n r hr hnpos hn
  rw [complex_unit_ball_volume_real] at h
  calc
    _ ≤ (n : ℝ)/Real.pi *
      (2*Real.pi*((r*Real.exp (-(n : ℝ)*rate 2 r))/
        ((n : ℝ)*(r-1/r)))) := h
    _ = _ := by
      field_simp [Real.pi_ne_zero, hnR.ne', ne_of_gt hc]

#print axioms realGinibreNonrealTailSimpleUpper
end SpectralRadiusUpperTail
