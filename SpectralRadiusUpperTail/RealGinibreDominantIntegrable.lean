import SpectralRadiusUpperTail.RealGinibreDominantDecay
import SpectralRadiusUpperTail.ExponentialRightTailEnvelope
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory Set

/-- The normalized Gamma cutoff is a measurable function of the radius. -/
theorem realGinibreGammaCutoff_measurable (n : ℕ) (hn : 3 ≤ n) :
    Measurable (fun r : ℝ =>
      (gammaMeasure (((n : ℝ)-1)/2) 1
        (Iic ((n : ℝ)*r^2/2))).toReal) := by
  have ha : (0 : ℝ) < ((n : ℝ)-1)/2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  let μ := gammaMeasure (((n : ℝ)-1)/2) 1
  haveI : IsProbabilityMeasure μ :=
    isProbabilityMeasure_gammaMeasure ha (by norm_num)
  have hmono : Monotone (fun t : ℝ => (μ (Iic t)).toReal) := by
    intro a b hab
    exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (Iic_subset_Iic.mpr hab))
  have harg : Measurable (fun r : ℝ => (n : ℝ)*r^2/2) := by fun_prop
  exact hmono.measurable.comp harg

/-- The dominant real one-point term is integrable to the right of any
fixed radius above one, with no integrability premise in the interface. -/
theorem realGinibreDominantDensity_integrableOn (n : ℕ) (hn : 3 ≤ n)
    (r : ℝ) (hr : 1 < r) :
    IntegrableOn (fun x => realGinibreDominantDensity n x) (Ioi r) := by
  have hrpos : 0 < r := by linarith
  have hs : 0 < r - 1/r := by
    have hsq : 1 < r^2 := by nlinarith
    apply sub_pos.mpr
    apply (div_lt_iff₀ hrpos).mpr
    nlinarith
  have ha : 0 < (n : ℝ)*(r-1/r) :=
    mul_pos (Nat.cast_pos.mpr (by omega)) hs
  have henv := exponential_right_tail_envelope_integrableOn
    (realGinibreCoreDensity n r) ((n : ℝ)*(r-1/r)) r ha
  have hcore : Measurable (realGinibreCoreDensity n) := by
    unfold realGinibreCoreDensity
    fun_prop
  have hmeas : Measurable (realGinibreDominantDensity n) := by
    unfold realGinibreDominantDensity
    exact hcore.mul (realGinibreGammaCutoff_measurable n hn)
  apply henv.mono' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx1 : 1 ≤ x := by linarith [show r < x from hx]
  have hxpos : 0 < x := by linarith
  have hq := (realGinibreDominantDensity_bounds n hn x hx1).1
  have hqpos := realGinibreCoreDensity_pos n (by omega) x hxpos
  have hdom0 : 0 ≤ realGinibreDominantDensity n x :=
    (div_nonneg hqpos.le (Nat.cast_nonneg _)).trans hq
  have hqrpos := realGinibreCoreDensity_pos n (by omega) r hrpos
  have henv0 : 0 ≤ realGinibreCoreDensity n r *
      Real.exp (-((n : ℝ)*(r-1/r))*(x-r)) :=
    mul_nonneg hqrpos.le (Real.exp_pos _).le
  have hdecay : realGinibreDominantDensity n x ≤
      realGinibreCoreDensity n r *
        Real.exp (-((n : ℝ)*(r-1/r))*(x-r)) := by
    convert realGinibreDominantDensity_decay n hn r x hr (le_of_lt hx) using 1 <;> ring
  simpa only [Real.norm_eq_abs, abs_of_nonneg hdom0, abs_of_nonneg henv0]
    using hdecay

#print axioms realGinibreGammaCutoff_measurable
#print axioms realGinibreDominantDensity_integrableOn
end SpectralRadiusUpperTail
