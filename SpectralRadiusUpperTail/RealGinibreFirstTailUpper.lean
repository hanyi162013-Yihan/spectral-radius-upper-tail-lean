import SpectralRadiusUpperTail.RealGinibreFirstDecay
import SpectralRadiusUpperTail.ExponentialRightTailEnvelope
import SpectralRadiusUpperTail.RightTailIntegralComparison
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set

theorem realGinibreFirstDensity_measurable (n : ℕ) :
    Measurable (realGinibreFirstDensity n) := by
  unfold realGinibreFirstDensity ginibreExpPartial
  fun_prop

/-- The finite-Poisson part is integrable to the right of a fixed radius
above one. -/
theorem realGinibreFirstDensity_integrableOn (n : ℕ) (hn : 1 ≤ n)
    (r : ℝ) (hr : 1 < r) :
    IntegrableOn (realGinibreFirstDensity n) (Ioi r) := by
  have hrpos : 0 < r := by linarith
  have hs : 0 < r-1/r := by
    have hsq : 1 < r^2 := by nlinarith
    apply sub_pos.mpr
    apply (div_lt_iff₀ hrpos).mpr
    nlinarith
  have ha : 0 < 2*(n : ℝ)*(r-1/r) := by
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    positivity
  have henv := exponential_right_tail_envelope_integrableOn
    (Real.sqrt ((n : ℝ)/(2*Real.pi)) *
      Real.exp (-(n : ℝ)*rate 2 r))
    (2*(n : ℝ)*(r-1/r)) r ha
  apply henv.mono' (realGinibreFirstDensity_measurable n).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx1 : 1 ≤ x := by linarith [show r < x from hx]
  have hfirst0 := (realGinibreFirstDensity_bound n hn x hx1).1
  have henv0 : 0 ≤
      (Real.sqrt ((n : ℝ)/(2*Real.pi)) * Real.exp (-(n : ℝ)*rate 2 r)) *
        Real.exp (-(2*(n : ℝ)*(r-1/r))*(x-r)) := by positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg hfirst0, abs_of_nonneg henv0]
    using realGinibreFirstDensity_decay n hn r x hr (le_of_lt hx)

/-- The finite-Poisson part has a half-line integral with the faster
complex-rate exponent. -/
theorem realGinibreFirstTailUpper (n : ℕ) (hn : 1 ≤ n)
    (r : ℝ) (hr : 1 < r) :
    (∫ x : ℝ in Ioi r, realGinibreFirstDensity n x) ≤
      (Real.sqrt ((n : ℝ)/(2*Real.pi)) *
        Real.exp (-(n : ℝ)*rate 2 r)) /
          (2*(n : ℝ)*(r-1/r)) := by
  have hrpos : 0 < r := by linarith
  have hs : 0 < r-1/r := by
    have hsq : 1 < r^2 := by nlinarith
    apply sub_pos.mpr
    apply (div_lt_iff₀ hrpos).mpr
    nlinarith
  have ha : 0 < 2*(n : ℝ)*(r-1/r) := by
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    positivity
  apply right_tail_integral_le_of_exp_envelope
    (realGinibreFirstDensity n) r
    (Real.sqrt ((n : ℝ)/(2*Real.pi)) * Real.exp (-(n : ℝ)*rate 2 r))
    (2*(n : ℝ)*(r-1/r)) ha
    (realGinibreFirstDensity_integrableOn n hn r hr)
  intro x hx
  exact realGinibreFirstDensity_decay n hn r x hr (le_of_lt hx)

#print axioms realGinibreFirstDensity_measurable
#print axioms realGinibreFirstDensity_integrableOn
#print axioms realGinibreFirstTailUpper
end SpectralRadiusUpperTail
