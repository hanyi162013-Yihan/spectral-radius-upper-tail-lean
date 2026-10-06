import SpectralRadiusUpperTail.RealGinibreWeightedCoreIntegrable
import SpectralRadiusUpperTail.RealGinibreWeightedCoreBudget
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set

/-- Beyond radius one, the polar Jacobian is absorbed by one extra square
power in the uncut real-Ginibre Gamma integral. -/
theorem realGinibre_radialCore_pointwise (n k : ℕ) (hn : 0 < n) (s : ℝ)
    (hs : 1 ≤ s) :
    s*(s^(2*k)*realGinibreCoreDensity n s) ≤
      s^(2*(k+1))*realGinibreCoreDensity n s := by
  have hs0 : 0 ≤ s := by linarith
  have hs2 : s ≤ s^2 := by nlinarith [sq_nonneg (s-1)]
  have hp : 0 ≤ s^(2*k) := pow_nonneg hs0 _
  have hpower : s*s^(2*k) ≤ s^(2*(k+1)) := by
    calc
      _ ≤ s^2*s^(2*k) := mul_le_mul_of_nonneg_right hs2 hp
      _ = _ := by
        have harg : 2*(k+1) = 2*k+2 := by omega
        rw [harg, pow_add]
        ring
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hpower
    (realGinibreCoreDensity_pos n hn s (by linarith)).le

theorem realGinibre_radialCore_integrableOn (n k : ℕ)
    (hn : 0 < n) :
    IntegrableOn (fun s : ℝ =>
      s*(s^(2*k)*realGinibreCoreDensity n s)) (Ioi 1) := by
  have hnext := (realGinibreCoreDensity_weighted_integrableOn
    n (k+1) hn).mono_set (show Ioi (1 : ℝ) ⊆ Ioi 0 by
      intro s hs
      exact lt_trans (by norm_num : (0 : ℝ) < 1) hs)
  have hmeas : Measurable (fun s : ℝ =>
      s*(s^(2*k)*realGinibreCoreDensity n s)) := by
    unfold realGinibreCoreDensity
    fun_prop
  apply hnext.mono' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs1 : 1 ≤ s := le_of_lt hs
  have hs0 : 0 ≤ s := by linarith
  have hQ := (realGinibreCoreDensity_pos n hn s (by linarith)).le
  have hleft : 0 ≤ s*(s^(2*k)*realGinibreCoreDensity n s) := by
    exact mul_nonneg hs0 (mul_nonneg (pow_nonneg hs0 _) hQ)
  have hright : 0 ≤ s^(2*(k+1))*realGinibreCoreDensity n s := by
    exact mul_nonneg (pow_nonneg hs0 _) hQ
  simpa only [Real.norm_eq_abs, abs_of_nonneg hleft,
    abs_of_nonneg hright] using realGinibre_radialCore_pointwise n k hn s hs1

theorem realGinibre_radialCore_integral_upper (n k : ℕ)
    (hn : 0 < n) :
    (∫ s in Ioi (1 : ℝ),
      s*(s^(2*k)*realGinibreCoreDensity n s)) ≤
        Real.exp (realGinibreWeightedUpperExponent n (k+1)) := by
  have hrad := realGinibre_radialCore_integrableOn n k hn
  have hcore := realGinibreCoreDensity_weighted_integrableOn n (k+1) hn
  have hcore1 := hcore.mono_set (show Ioi (1 : ℝ) ⊆ Ioi 0 by
    intro s hs
    exact lt_trans (by norm_num : (0 : ℝ) < 1) hs)
  have hfirst := setIntegral_mono_on hrad hcore1 measurableSet_Ioi
    (fun s hs => realGinibre_radialCore_pointwise n k hn s (le_of_lt hs))
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun s => s^(2*(k+1))*realGinibreCoreDensity n s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact mul_nonneg (pow_nonneg (le_of_lt hs) _)
      (realGinibreCoreDensity_pos n hn s hs).le
  have hsubset : Ioi (1 : ℝ) ⊆ Ioi 0 := by
    intro s hs
    exact lt_trans (by norm_num : (0 : ℝ) < 1) hs
  have hsecond := setIntegral_mono_set hcore hnonneg hsubset.eventuallyLE
  exact hfirst.trans (hsecond.trans
    (realGinibreCoreDensity_weighted_upper n (k+1) hn))

#print axioms realGinibre_radialCore_pointwise
#print axioms realGinibre_radialCore_integrableOn
#print axioms realGinibre_radialCore_integral_upper
end SpectralRadiusUpperTail
