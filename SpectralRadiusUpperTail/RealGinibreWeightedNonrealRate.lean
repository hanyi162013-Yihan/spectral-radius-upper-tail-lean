import SpectralRadiusUpperTail.RealGinibreWeightedNonrealUpper
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set Metric Filter
open scoped Topology

/-- The nonreal one-point expression has at most the real-Ginibre
linear-power exponent. The polar Jacobian changes the power by one, which
does not change its speed-`n` rate. -/
theorem realGinibreNonrealDensityAt_weighted_upper_eventual
    (k : ℕ → ℕ) (α : ℝ) (hα : 0 < α)
    (hk : Tendsto (fun n => (k n : ℝ)/(n : ℝ)) atTop (𝓝 α))
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      (∫ z : ℂ in {z | 1 < ‖z‖},
        ‖z‖^(2*k n)*realGinibreNonrealDensityAt n z) ≤
          Real.exp ((n : ℝ)*(powerRate 1 α+δ)) := by
  let ε : ℝ := δ/3
  let C : ℝ := 2*(volume : Measure ℂ).real (ball 0 1)
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hOne : Tendsto (fun n : ℕ => (1 : ℝ)/(n : ℝ))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hsum := hk.add hOne
  have hplus : Tendsto (fun n : ℕ => ((k n+1 : ℕ) : ℝ)/(n : ℝ))
      atTop (𝓝 α) := by
    simpa only [add_zero] using hsum.congr' (by
      filter_upwards [] with n
      push_cast
      ring)
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    realGinibre_first_core_prefactor_eventual ε hε,
    realGinibreWeightedUpperExponent_eventual (fun n => k n+1)
      α hα hplus ε hε,
    eventually_exp_prefactor_absorb C (powerRate 1 α+2*ε) ε hC hε]
    with n hn hbudget hgamma habsorb
  have hfinite := realGinibreNonrealDensityAt_weighted_upper_of_budget
    n (k n) hn ε hbudget
  calc
    _ ≤ C*Real.exp ((n : ℝ)*ε)*
        Real.exp (realGinibreWeightedUpperExponent n (k n+1)) := by
      simpa only [C] using hfinite
    _ ≤ C*Real.exp ((n : ℝ)*ε)*
        Real.exp ((n : ℝ)*(powerRate 1 α+ε)) := by
      exact mul_le_mul_of_nonneg_left hgamma
        (mul_nonneg hC (Real.exp_pos _).le)
    _ = C*Real.exp ((n : ℝ)*(powerRate 1 α+2*ε)) := by
      rw [mul_assoc, ← Real.exp_add]
      ring
    _ ≤ Real.exp ((n : ℝ)*(powerRate 1 α+2*ε+ε)) := habsorb
    _ = _ := by congr 1; dsimp [ε]; ring

#print axioms realGinibreNonrealDensityAt_weighted_upper_eventual
end SpectralRadiusUpperTail
