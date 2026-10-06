import SpectralRadiusUpperTail.RealGinibreCoreDensity
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

/-- The normalization gap between the finite-Poisson envelope and the
uncut dominant real one-point factor is subexponential. -/
theorem realGinibre_first_core_prefactor_rate :
    Tendsto (fun n : ℕ =>
      (Real.log (n : ℝ)-Real.log (realGinibreCoreDensity n 1)+1/2)/
        (n : ℝ)) atTop (𝓝 0) := by
  have hlogn : Tendsto (fun n : ℕ => Real.log (n : ℝ)/(n : ℝ))
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  have hcore : Tendsto (fun n : ℕ =>
      Real.log (realGinibreCoreDensity n 1)/(n : ℝ)) atTop (𝓝 0) := by
    simpa [rate, Real.log_one] using
      realGinibreCoreDensity_log_rate 1 (by norm_num)
  have hconst : Tendsto (fun n : ℕ => (1/2 : ℝ)/(n : ℝ))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hh := (hlogn.sub hcore).add hconst
  simpa only [sub_zero, zero_add] using hh.congr' (by
    filter_upwards [] with n
    ring)

theorem realGinibre_first_core_prefactor_eventual
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (n : ℝ)-Real.log (realGinibreCoreDensity n 1)+1/2 ≤
        (n : ℝ)*ε := by
  have ht := realGinibre_first_core_prefactor_rate
  filter_upwards [(tendsto_order.mp ht).2 ε hε,
    eventually_gt_atTop 0] with n hn hn0
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  simpa only [mul_comm] using ((div_lt_iff₀ hnR).mp hn).le

#print axioms realGinibre_first_core_prefactor_rate
#print axioms realGinibre_first_core_prefactor_eventual
end SpectralRadiusUpperTail
