import SpectralRadiusUpperTail.PlanarRadialPoissonIdentity
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set Metric

/-- The planar exterior Poisson envelope has rate `-I₂(r)`; the
polar Jacobian costs only a fixed radial prefactor. -/
theorem planarPoissonTailUpper (n : ℕ) (r : ℝ)
    (hr : 1 < r) (hnpos : 0 < n)
    (hn : 1/r ≤ (n : ℝ)*(r-1/r)) :
    (∫ z : ℂ in {z | r < ‖z‖}, Real.exp (-(n : ℝ)*rate 2 ‖z‖)) ≤
      2 * (volume : Measure ℂ).real (ball 0 1) *
        ((r * Real.exp (-(n : ℝ)*rate 2 r)) /
          ((n : ℝ)*(r-1/r))) := by
  rw [planarRadialPoissonIdentity n r (by linarith)]
  exact mul_le_mul_of_nonneg_left
    (realGinibreRadialTailUpper n r hr hn hnpos)
    (by positivity)

#print axioms planarPoissonTailUpper
end SpectralRadiusUpperTail
