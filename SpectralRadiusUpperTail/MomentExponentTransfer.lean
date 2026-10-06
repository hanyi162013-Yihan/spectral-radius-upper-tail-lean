import SpectralRadiusUpperTail.Rate
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

/-- The integer power selection has the prescribed positive linear scale. -/
lemma floor_linear_power_ratio (α : ℝ) (hα : 0 < α) :
    Tendsto (fun n : ℕ => (⌊α*(n : ℝ)⌋₊ : ℝ)/(n : ℝ)) atTop (𝓝 α) := by
  have ht : Tendsto (fun n : ℕ => α*(n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hα
  have hh := (tendsto_nat_floor_div_atTop.comp ht).mul_const α
  rw [one_mul] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  dsimp
  field_simp

lemma floor_linear_power_eventually_pos (α : ℝ) (hα : 0 < α) :
    ∀ᶠ n : ℕ in atTop, 0 < ⌊α*(n : ℝ)⌋₊ := by
  have ht : Tendsto (fun n : ℕ => α*(n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hα
  filter_upwards [ht.eventually (eventually_ge_atTop 1)] with n hn
  exact Nat.floor_pos.mpr hn

/-- Gaussian moment growth and a finite Markov comparison imply the expected
exponential tail bound for any sequence of powers with k_n/n -> α. -/
lemma moment_exponent_transfer (p M : ℕ → ℝ) (k : ℕ → ℕ)
    (α F r : ℝ) (hr : 0 < r)
    (hk : Tendsto (fun n => (k n : ℝ)/(n : ℝ)) atTop (𝓝 α))
    (hmarkov : ∀ᶠ n : ℕ in atTop, p n ≤ M n/r^(2*k n))
    (hmoment : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      M n ≤ Real.exp ((n : ℝ)*(F+δ)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      p n ≤ Real.exp ((n : ℝ)*(F-2*α*Real.log r+ε)) := by
  have ht : Tendsto (fun n => 2*((k n : ℝ)/(n : ℝ))*Real.log r) atTop
      (𝓝 (2*α*Real.log r)) := (hk.const_mul 2).mul_const _
  have he := (tendsto_order.mp ht).1 (2*α*Real.log r-ε/2) (by linarith)
  filter_upwards [hmarkov, hmoment (ε/2) (by positivity), he,
    eventually_gt_atTop 0] with n hn hm he hn0
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  have hpow : r^(2*k n) = Real.exp (2*(k n : ℝ)*Real.log r) := by
    rw [show 2*(k n : ℝ) = ((2*k n : ℕ) : ℝ) by push_cast; ring,
      Real.exp_nat_mul, Real.exp_log hr]
  calc
    p n ≤ M n/r^(2*k n) := hn
    _ ≤ Real.exp ((n : ℝ)*(F+ε/2))/r^(2*k n) :=
      div_le_div_of_nonneg_right hm (pow_nonneg hr.le _)
    _ = Real.exp ((n : ℝ)*(F+ε/2)-2*(k n : ℝ)*Real.log r) := by rw [hpow, Real.exp_sub]
    _ ≤ Real.exp ((n : ℝ)*(F-2*α*Real.log r+ε)) := by
      apply Real.exp_le_exp.mpr
      have hx := mul_le_mul_of_nonneg_left he.le hnR.le
      have hc : (n : ℝ)*(2*((k n : ℝ)/(n : ℝ))*Real.log r) =
          2*(k n : ℝ)*Real.log r := by field_simp
      rw [hc] at hx
      nlinarith

/-- Only the upper Gaussian moment asymptotic is needed for the sharp upper
tail; the exact dual optimizer is already proved in Rate. -/
lemma sharp_tail_of_power_moments (p : ℕ → ℝ) (M : ℕ → ℕ → ℝ)
    (β r : ℝ) (hβ : 0 < β) (hr : 1 < r)
    (hmarkov : ∀ α : ℝ, 0 < α → ∀ᶠ n : ℕ in atTop,
      p n ≤ M n ⌊α*(n : ℝ)⌋₊/r^(2*⌊α*(n : ℝ)⌋₊))
    (hmoment : ∀ α : ℝ, 0 < α → ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      M n ⌊α*(n : ℝ)⌋₊ ≤ Real.exp ((n : ℝ)*(powerRate β α+δ)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, p n ≤ Real.exp ((n : ℝ)*(-rate β r+ε)) := by
  let α := β/2*(r^2-1)
  have hα : 0 < α := optimizer_positive β r hβ hr
  have hh := moment_exponent_transfer p (fun n => M n ⌊α*(n : ℝ)⌋₊)
    (fun n => ⌊α*(n : ℝ)⌋₊) α (powerRate β α) r (by linarith)
    (floor_linear_power_ratio α hα) (hmarkov α hα) (hmoment α hα) ε hε
  simpa only [α, dual_at_optimizer β r hβ.ne'] using hh

#print axioms floor_linear_power_ratio
#print axioms moment_exponent_transfer
#print axioms sharp_tail_of_power_moments
end SpectralRadiusUpperTail
