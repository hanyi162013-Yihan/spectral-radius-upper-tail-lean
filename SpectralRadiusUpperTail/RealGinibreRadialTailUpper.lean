import SpectralRadiusUpperTail.RealGinibreRadialDecay
import SpectralRadiusUpperTail.RightTailIntegralComparison
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set

/-- The radial exterior Poisson envelope is integrable. -/
theorem realGinibreRadial_integrableOn (n : ℕ) (r : ℝ)
    (hr : 1 < r) (hn : 1/r ≤ (n : ℝ)*(r-1/r))
    (hnpos : 0 < n) :
    IntegrableOn (fun s : ℝ => s * Real.exp (-(n : ℝ)*rate 2 s))
      (Ioi r) := by
  have hrpos : 0 < r := by linarith
  have hs : 0 < r-1/r := by
    have hsq : 1 < r^2 := by nlinarith
    apply sub_pos.mpr
    apply (div_lt_iff₀ hrpos).mpr
    nlinarith
  have ha : 0 < (n : ℝ)*(r-1/r) := by positivity
  have henv := exponential_right_tail_envelope_integrableOn
    (r*Real.exp (-(n : ℝ)*rate 2 r))
    ((n : ℝ)*(r-1/r)) r ha
  have hmeas : Measurable
      (fun s : ℝ => s * Real.exp (-(n : ℝ)*rate 2 s)) := by
    unfold rate
    fun_prop
  apply henv.mono' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hsr
  have hs0 : 0 ≤ s := by linarith [show r < s from hsr]
  have hb := realGinibreRadial_decay n r s hr (le_of_lt hsr) hn
  have hright : 0 ≤ r * Real.exp (-(n : ℝ)*rate 2 r) *
      Real.exp (-((n : ℝ)*(r-1/r))*(s-r)) := by positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hs0 (Real.exp_pos _).le),
    abs_of_nonneg hright] using hb

/-- The radial Jacobian in the nonreal planar first moment contributes
only a bounded prefactor outside a fixed disk. -/
theorem realGinibreRadialTailUpper (n : ℕ) (r : ℝ)
    (hr : 1 < r) (hn : 1/r ≤ (n : ℝ)*(r-1/r))
    (hnpos : 0 < n) :
    (∫ s : ℝ in Ioi r, s * Real.exp (-(n : ℝ)*rate 2 s)) ≤
      (r * Real.exp (-(n : ℝ)*rate 2 r)) /
        ((n : ℝ)*(r-1/r)) := by
  have hrpos : 0 < r := by linarith
  have hs : 0 < r-1/r := by
    have hsq : 1 < r^2 := by nlinarith
    apply sub_pos.mpr
    apply (div_lt_iff₀ hrpos).mpr
    nlinarith
  have ha : 0 < (n : ℝ)*(r-1/r) := by positivity
  have hf := realGinibreRadial_integrableOn n r hr hn hnpos
  apply right_tail_integral_le_of_exp_envelope _ r _ _ ha hf
  intro s hsr
  exact realGinibreRadial_decay n r s hr (le_of_lt hsr) hn

#print axioms realGinibreRadial_integrableOn
#print axioms realGinibreRadialTailUpper
end SpectralRadiusUpperTail
