import SpectralRadiusUpperTail.MarkedRealGaussianCharpolyMomentReal
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- The actual Gaussian moment in the fixed-chart formula differs from
its leading scalar power by at most a polynomial dimension factor
outside the circular scale. -/
theorem markedRealGaussianCharpolyMoment_exterior_bounds
    (m : ℕ) (x : ℝ) (hx : 0 < x) (hscale : (m : ℝ) ≤ x^2) :
    ENNReal.ofReal (x^m) ≤ markedRealGaussianCharpolyMoment m x ∧
      markedRealGaussianCharpolyMoment m x ≤
        ENNReal.ofReal (((m : ℝ)+2)/2 * x^m) := by
  obtain ⟨hl, hu⟩ :=
    gaussian_charpoly_absolute_moment_exterior_bound
      (ι := Fin m) x hx (by simpa using hscale)
  rw [markedRealGaussianCharpolyMoment_eq_ofReal_integral]
  exact ⟨ENNReal.ofReal_le_ofReal
      (by simpa only [Fintype.card_fin] using hl),
    ENNReal.ofReal_le_ofReal
      (by simpa only [Fintype.card_fin] using hu)⟩

#print axioms markedRealGaussianCharpolyMoment_exterior_bounds
end SpectralRadiusUpperTail
