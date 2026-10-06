import SpectralRadiusUpperTail.GinibrePoissonSharp
import SpectralRadiusUpperTail.Rate

namespace SpectralRadiusUpperTail

/-- The Poisson part of the Ginibre one-point intensity decays at the
complex rate `2 I₁(r)` outside the unit disk. -/
theorem ginibre_poisson_radius_bound (n : ℕ) (r : ℝ) (hr : 1 ≤ r) :
    Real.exp (-(n : ℝ)*r^2) * ginibreExpPartial n ((n : ℝ)*r^2) ≤
      Real.exp (-(n : ℝ)*rate 2 r) := by
  have h := ginibrePoissonCutoff_sharp n
    (u := r^2) (by nlinarith)
  have hrpos : 0 < r := by linarith
  have he : (n : ℝ)*(1+Real.log (r^2)-r^2) = -(n : ℝ)*rate 2 r := by
    rw [Real.log_pow]
    unfold rate
    ring
  rw [he] at h
  exact h

#print axioms ginibre_poisson_radius_bound
end SpectralRadiusUpperTail
