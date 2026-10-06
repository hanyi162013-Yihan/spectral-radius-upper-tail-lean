import SpectralRadiusUpperTail.ExponentialBoundsLogLimit
import Mathlib.Order.LiminfLimsup

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

/-- A probability lower bound in exponential form gives the ordinary real
logarithmic liminf, with positivity established before taking logarithms. -/
lemma log_liminf_of_exponential_lower (p : ℕ → ℝ) (L : ℝ)
    (hpos : ∀ n, 0 ≤ p n) (hone : ∀ n, p n ≤ 1)
    (hlower : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      Real.exp ((n : ℝ)*(L-ε)) ≤ p n) :
    L ≤ liminf (fun n => Real.log (p n)/(n : ℝ)) atTop := by
  have hlog (ε : ℝ) (hε : 0 < ε) : ∀ᶠ n : ℕ in atTop,
      L-ε ≤ Real.log (p n)/(n : ℝ) := by
    filter_upwards [hlower ε hε, eventually_gt_atTop 0] with n hn hn0
    have hh := Real.log_le_log (Real.exp_pos _) hn
    rw [Real.log_exp] at hh
    exact (le_div_iff₀ (Nat.cast_pos.mpr hn0)).mpr (by simpa only [mul_comm] using hh)
  have hu : atTop.IsBoundedUnder (· ≤ ·) (fun n => Real.log (p n)/(n : ℝ)) := by
    refine ⟨0, ?_⟩
    change ∀ᶠ n : ℕ in atTop, Real.log (p n)/(n : ℝ) ≤ 0
    exact Eventually.of_forall (fun n => div_nonpos_of_nonpos_of_nonneg
      (Real.log_nonpos (hpos n) (hone n)) (Nat.cast_nonneg n))
  have hl : atTop.IsBoundedUnder (· ≥ ·) (fun n => Real.log (p n)/(n : ℝ)) :=
    ⟨L-1, hlog 1 zero_lt_one⟩
  apply (le_liminf_iff hu.isCoboundedUnder_ge hl).mpr
  intro y hy
  filter_upwards [hlog ((L-y)/2) (by linarith)] with n hn
  linarith

#print axioms log_liminf_of_exponential_lower
end SpectralRadiusUpperTail
