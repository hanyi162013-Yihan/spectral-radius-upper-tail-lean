import SpectralRadiusUpperTail.RealGinibreFirstCoreCompare
import SpectralRadiusUpperTail.RealGinibreFirstTailUpper
import SpectralRadiusUpperTail.RealGinibreWeightedCoreIntegrable
import SpectralRadiusUpperTail.RealGinibreWeightedCoreBudget
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set Filter
open scoped Topology

/-- A finite-dimensional prefactor budget transfers the exact Gamma bound
to the weighted finite-Poisson real one-point term. -/
theorem realGinibreFirstDensity_weighted_upper_of_budget
    (n k : ℕ) (hn : 1 ≤ n) (ε : ℝ)
    (hbudget : Real.log (n : ℝ)-
        Real.log (realGinibreCoreDensity n 1)+1/2 ≤ (n : ℝ)*ε) :
    (∫ x in Ioi (1 : ℝ), x^(2*k)*realGinibreFirstDensity n x) ≤
      Real.exp ((n : ℝ)*ε)*
        Real.exp (realGinibreWeightedUpperExponent n k) := by
  let M := Real.exp ((n : ℝ)*ε)
  have hM : 0 ≤ M := (Real.exp_pos _).le
  have hcore := realGinibreCoreDensity_weighted_integrableOn n k (by omega)
  have hcore1 := hcore.mono_set (show Ioi (1 : ℝ) ⊆ Ioi 0 by
    intro x hx
    exact lt_trans (by norm_num : (0 : ℝ) < 1) hx)
  have henv : IntegrableOn
      (fun x : ℝ => M*(x^(2*k)*realGinibreCoreDensity n x))
      (Ioi 1) := hcore1.const_mul M
  have hmeas : Measurable
      (fun x : ℝ => x^(2*k)*realGinibreFirstDensity n x) := by
    exact (measurable_id.pow_const _).mul (realGinibreFirstDensity_measurable n)
  have hfirst : IntegrableOn
      (fun x : ℝ => x^(2*k)*realGinibreFirstDensity n x)
      (Ioi 1) := by
    apply henv.mono' hmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : 1 ≤ x := le_of_lt hx
    have hpow : 0 ≤ x^(2*k) := pow_nonneg (by linarith) _
    have hfirst0 := (realGinibreFirstDensity_bound n hn x hx1).1
    have hcore0 := (realGinibreCoreDensity_pos n (by omega) x (by linarith)).le
    have hpoint := realGinibreFirstDensity_le_exp_core_of_budget
      n hn ε hbudget x hx1
    have hle := mul_le_mul_of_nonneg_left hpoint hpow
    have hle' : x^(2*k)*realGinibreFirstDensity n x ≤
        M*(x^(2*k)*realGinibreCoreDensity n x) := by
      calc
        _ ≤ x^(2*k)*(Real.exp ((n : ℝ)*ε)*realGinibreCoreDensity n x) := hle
        _ = _ := by dsimp [M]; ring
    simpa only [M, mul_assoc, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hpow hfirst0),
      abs_of_nonneg (mul_nonneg hM (mul_nonneg hpow hcore0))]
      using hle'
  have hmono := setIntegral_mono_on hfirst henv measurableSet_Ioi
    (fun x hx => by
      have hle := mul_le_mul_of_nonneg_left
        (realGinibreFirstDensity_le_exp_core_of_budget n hn ε hbudget x
          (le_of_lt hx))
        (pow_nonneg (le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 1) hx))
          (2*k))
      calc
        x^(2*k)*realGinibreFirstDensity n x ≤
            x^(2*k)*(Real.exp ((n : ℝ)*ε)*realGinibreCoreDensity n x) := hle
        _ = M*(x^(2*k)*realGinibreCoreDensity n x) := by dsimp [M]; ring)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun x => x^(2*k)*realGinibreCoreDensity n x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (pow_nonneg (le_of_lt hx) _)
      (realGinibreCoreDensity_pos n (by omega) x hx).le
  have hsubset : Ioi (1 : ℝ) ⊆ Ioi 0 := by
    intro x hx
    exact lt_trans (by norm_num : (0 : ℝ) < 1) hx
  have hrestrict := setIntegral_mono_set hcore hnonneg hsubset.eventuallyLE
  calc
    _ ≤ M*(∫ x in Ioi (1 : ℝ),
        x^(2*k)*realGinibreCoreDensity n x) := by
      simpa only [integral_const_mul] using hmono
    _ ≤ M*(∫ x in Ioi (0 : ℝ),
        x^(2*k)*realGinibreCoreDensity n x) :=
      mul_le_mul_of_nonneg_left hrestrict hM
    _ ≤ M*Real.exp (realGinibreWeightedUpperExponent n k) :=
      mul_le_mul_of_nonneg_left
        (realGinibreCoreDensity_weighted_upper n k (by omega)) hM
    _ = _ := rfl

/-- The finite-Poisson real one-point term has no larger linear-power
speed-`n` exponent than the dominant real term. -/
theorem realGinibreFirstDensity_weighted_upper_eventual
    (k : ℕ → ℕ) (α : ℝ) (hα : 0 < α)
    (hk : Tendsto (fun n => (k n : ℝ)/(n : ℝ)) atTop (𝓝 α))
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      (∫ x in Ioi (1 : ℝ),
        x^(2*k n)*realGinibreFirstDensity n x) ≤
          Real.exp ((n : ℝ)*(powerRate 1 α+δ)) := by
  let ε : ℝ := δ/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    realGinibre_first_core_prefactor_eventual ε hε,
    realGinibreWeightedUpperExponent_eventual k α hα hk ε hε]
    with n hn hbudget hgamma
  have h := realGinibreFirstDensity_weighted_upper_of_budget
    n (k n) hn ε hbudget
  calc
    _ ≤ Real.exp ((n : ℝ)*ε)*
        Real.exp (realGinibreWeightedUpperExponent n (k n)) := h
    _ ≤ Real.exp ((n : ℝ)*ε)*
        Real.exp ((n : ℝ)*(powerRate 1 α+ε)) :=
      mul_le_mul_of_nonneg_left hgamma (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [ε]; ring

#print axioms realGinibreFirstDensity_weighted_upper_of_budget
#print axioms realGinibreFirstDensity_weighted_upper_eventual
end SpectralRadiusUpperTail
