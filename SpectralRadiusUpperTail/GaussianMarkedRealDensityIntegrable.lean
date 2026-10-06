import SpectralRadiusUpperTail.GaussianMarkedRealDensityMeasurable
import SpectralRadiusUpperTail.RealGinibreWeightedCoreIntegrable
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set

/-- The polynomial-factor exterior bound makes the marked-eigenline
candidate integrable on every positive exterior ray. -/
theorem gaussianMarkedRealDensity_integrableOn
    (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : 1 < r) :
    IntegrableOn (gaussianMarkedRealDensity n) (Ioi r) := by
  have hrpos : 0 < r := by linarith
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hcore0 := realGinibreCoreDensity_weighted_integrableOn n 0 hn
  simp only [mul_zero, pow_zero, one_mul] at hcore0
  have hcore : IntegrableOn (realGinibreCoreDensity n) (Ioi r) :=
    hcore0.mono_set (by intro x hx; exact lt_trans hrpos hx)
  have henv := hcore.const_mul (n : ℝ)
  apply henv.mono' (measurable_gaussianMarkedRealDensity n).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx1 : 1 ≤ x := by linarith [show r < x from hx]
  have hxpos : 0 < x := by linarith
  have hq := realGinibreCoreDensity_pos n hn x hxpos
  obtain ⟨hl, hu⟩ := gaussianMarkedRealDensity_sandwich n hn x hx1
  have hcand : 0 ≤ gaussianMarkedRealDensity n x := hq.le.trans hl
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpoly : ((n : ℝ)+1)/2 ≤ (n : ℝ) := by linarith
  have hbound : gaussianMarkedRealDensity n x ≤
      (n : ℝ)*realGinibreCoreDensity n x :=
    hu.trans (mul_le_mul_of_nonneg_right hpoly hq.le)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hcand,
    abs_of_nonneg (mul_nonneg hnR hq.le)] using hbound

#print axioms gaussianMarkedRealDensity_integrableOn
end SpectralRadiusUpperTail
