import SpectralRadiusUpperTail.RealGinibreCoreDensity
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- Put the weighted uncut real-Ginibre factor into the standard Gamma
integrand form. The real and natural square powers are made explicit. -/
theorem realGinibreCoreDensity_weighted_pointwise (n k : ℕ)
    (x : ℝ) (hx : 0 < x) :
    x^(2*k) * realGinibreCoreDensity n x =
      (((n : ℝ)/2)^((n : ℝ)/2)/Real.Gamma ((n : ℝ)/2)) *
        (x^((n : ℝ)-1+2*(k : ℝ)) *
          Real.exp (-((n : ℝ)/2)*x^(2 : ℝ))) := by
  let b : ℝ := (n : ℝ)/2
  let q : ℝ := (n : ℝ)-1+2*(k : ℝ)
  let C : ℝ := b^((n : ℝ)/2)/Real.Gamma ((n : ℝ)/2)
  have hpow : x^(2*k) * x^((n : ℝ)-1) = x^q := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hx]
    congr 1
    dsimp [q]
    push_cast
    ring
  have hxpow : x^(2 : ℝ) = x^(2 : ℕ) := by
    simpa only [Nat.cast_ofNat] using (Real.rpow_natCast x 2)
  have hE : Real.exp (-(n : ℝ)*x^2/2) =
      Real.exp (-b*x^(2 : ℝ)) := by
    rw [hxpow]
    congr 1
    dsimp [b]
    ring
  dsimp [realGinibreCoreDensity, C, b, q]
  rw [hE, ← hpow]
  ring

#print axioms realGinibreCoreDensity_weighted_pointwise
end SpectralRadiusUpperTail
