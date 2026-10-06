import SpectralRadiusUpperTail.RealGinibreWeightedCoreIntegrable
import SpectralRadiusUpperTail.RealGinibreWeightedCoreBudget
import SpectralRadiusUpperTail.RealGinibreDominantIntegrable
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set Filter
open scoped Topology

/-- The cutoff in the dominant real one-point term preserves the weighted
integrability beyond the unit radius. -/
theorem realGinibreDominantDensity_weighted_integrableOn
    (n k : ℕ) (hn : 3 ≤ n) :
    IntegrableOn (fun x : ℝ => x^(2*k)*realGinibreDominantDensity n x)
      (Ioi 1) := by
  have hcore := (realGinibreCoreDensity_weighted_integrableOn n k
    (by omega)).mono_set (show Ioi (1 : ℝ) ⊆ Ioi 0 by
      intro x hx
      exact lt_trans (by norm_num : (0 : ℝ) < 1) hx)
  have hcoreMeas : Measurable (realGinibreCoreDensity n) := by
    unfold realGinibreCoreDensity
    fun_prop
  have hdomMeas : Measurable (realGinibreDominantDensity n) := by
    unfold realGinibreDominantDensity
    exact hcoreMeas.mul (realGinibreGammaCutoff_measurable n hn)
  have hmeas : Measurable
      (fun x : ℝ => x^(2*k)*realGinibreDominantDensity n x) := by
    fun_prop
  apply hcore.mono' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx1 : 1 ≤ x := le_of_lt hx
  have hxpos : 0 < x := by linarith
  have hpow : 0 ≤ x^(2*k) := pow_nonneg hxpos.le _
  have hbound := realGinibreDominantDensity_bounds n hn x hx1
  have hcorepos := (realGinibreCoreDensity_pos n (by omega) x hxpos).le
  have hdompos : 0 ≤ realGinibreDominantDensity n x :=
    (div_nonneg hcorepos (Nat.cast_nonneg _)).trans hbound.1
  have hle := mul_le_mul_of_nonneg_left hbound.2 hpow
  simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hpow hdompos),
    abs_of_nonneg (mul_nonneg hpow hcorepos)] using hle

/-- The weighted dominant real one-point contribution is bounded by the
exact uncut Gamma integral. -/
theorem realGinibreDominantDensity_weighted_upper
    (n k : ℕ) (hn : 3 ≤ n) :
    (∫ x in Ioi (1 : ℝ), x^(2*k)*realGinibreDominantDensity n x) ≤
      Real.exp (realGinibreWeightedUpperExponent n k) := by
  have hcore := realGinibreCoreDensity_weighted_integrableOn n k (by omega)
  have hcore1 := hcore.mono_set (show Ioi (1 : ℝ) ⊆ Ioi 0 by
    intro x hx
    exact lt_trans (by norm_num : (0 : ℝ) < 1) hx)
  have hdom := realGinibreDominantDensity_weighted_integrableOn n k hn
  have hpoint (x : ℝ) (hx : x ∈ Ioi (1 : ℝ)) :
      x^(2*k)*realGinibreDominantDensity n x ≤
        x^(2*k)*realGinibreCoreDensity n x := by
    exact mul_le_mul_of_nonneg_left
      (realGinibreDominantDensity_bounds n hn x (le_of_lt hx)).2
      (pow_nonneg (le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 1) hx)) _)
  have hfirst := setIntegral_mono_on hdom hcore1 measurableSet_Ioi hpoint
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun x => x^(2*k)*realGinibreCoreDensity n x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (pow_nonneg (le_of_lt hx) _)
      (realGinibreCoreDensity_pos n (by omega) x hx).le
  have hsubset : Ioi (1 : ℝ) ⊆ Ioi 0 := by
    intro x hx
    exact lt_trans (by norm_num : (0 : ℝ) < 1) hx
  have hsecond := setIntegral_mono_set hcore hnonneg hsubset.eventuallyLE
  exact hfirst.trans (hsecond.trans
    (realGinibreCoreDensity_weighted_upper n k (by omega)))

/-- The dominant real one-point term has the candidate weighted upper
exponent at every positive linear power scale. -/
theorem realGinibreDominantDensity_weighted_upper_eventual
    (k : ℕ → ℕ) (α : ℝ) (hα : 0 < α)
    (hk : Tendsto (fun n => (k n : ℝ)/(n : ℝ)) atTop (𝓝 α))
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      (∫ x in Ioi (1 : ℝ),
        x^(2*k n)*realGinibreDominantDensity n x) ≤
          Real.exp ((n : ℝ)*(powerRate 1 α+δ)) := by
  filter_upwards [eventually_ge_atTop (3 : ℕ),
    realGinibreWeightedUpperExponent_eventual k α hα hk δ hδ]
    with n hn hupper
  exact (realGinibreDominantDensity_weighted_upper n (k n) hn).trans hupper

#print axioms realGinibreDominantDensity_weighted_integrableOn
#print axioms realGinibreDominantDensity_weighted_upper
#print axioms realGinibreDominantDensity_weighted_upper_eventual
end SpectralRadiusUpperTail
