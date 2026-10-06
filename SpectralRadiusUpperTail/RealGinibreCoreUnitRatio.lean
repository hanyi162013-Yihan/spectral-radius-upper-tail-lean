import SpectralRadiusUpperTail.RealGinibreCoreDensity
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- The uncut real one-point factor has an exact radial log ratio relative
to the unit radius. -/
theorem realGinibreCoreDensity_log_unit_ratio (n : ℕ) (hn : 0 < n)
    (r : ℝ) (hr : 0 < r) :
    Real.log (realGinibreCoreDensity n r) =
      Real.log (realGinibreCoreDensity n 1) -
        (n : ℝ)*rate 1 r - Real.log r := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hdiff :
      Real.log (realGinibreCoreDensity n r)/(n : ℝ) -
        Real.log (realGinibreCoreDensity n 1)/(n : ℝ) =
          -rate 1 r - Real.log r/(n : ℝ) := by
    rw [realGinibreCoreDensity_log n hn r hr,
      realGinibreCoreDensity_log n hn 1 (by norm_num)]
    unfold realGinibreGammaLogCore rate
    simp only [Real.log_one, mul_zero]
    field_simp [hnR.ne']
    ring
  have hdiv : Real.log (realGinibreCoreDensity n r)/(n : ℝ) =
      Real.log (realGinibreCoreDensity n 1)/(n : ℝ) -
        rate 1 r - Real.log r/(n : ℝ) := by linarith
  calc
    Real.log (realGinibreCoreDensity n r) =
        (Real.log (realGinibreCoreDensity n r)/(n : ℝ))*(n : ℝ) := by
          field_simp
    _ = (Real.log (realGinibreCoreDensity n 1)/(n : ℝ) -
        rate 1 r - Real.log r/(n : ℝ))*(n : ℝ) := by rw [hdiv]
    _ = _ := by field_simp

#print axioms realGinibreCoreDensity_log_unit_ratio
end SpectralRadiusUpperTail
