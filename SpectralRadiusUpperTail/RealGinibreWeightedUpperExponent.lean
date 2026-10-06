import SpectralRadiusUpperTail.RealGinibreWeightedGammaRate

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

/-- The exact logarithmic envelope for the weighted dominant real-Ginibre
one-point integral, after shifting both Gamma arguments up by one. -/
noncomputable def realGinibreWeightedUpperExponent (n k : ℕ) : ℝ :=
  Real.log (Real.Gamma ((n : ℝ)/2+(k : ℝ)+1)) -
    Real.log (Real.Gamma ((n : ℝ)/2+1)) -
    (k : ℝ)*Real.log ((n : ℝ)/2) - Real.log 2

theorem realGinibreWeightedUpperExponent_rate (k : ℕ → ℕ) (α : ℝ)
    (hα : 0 < α)
    (hk : Tendsto (fun n => (k n : ℝ)/(n : ℝ)) atTop (𝓝 α)) :
    Tendsto (fun n => realGinibreWeightedUpperExponent n (k n)/(n : ℝ))
      atTop (𝓝 (powerRate 1 α)) := by
  have hb := realGinibre_weighted_gamma_log_rate k α hα hk
  have hc : Tendsto (fun n : ℕ => Real.log 2/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hh := hb.sub hc
  rw [sub_zero] at hh
  apply hh.congr'
  filter_upwards [] with n
  unfold realGinibreWeightedUpperExponent
  have harg : (((n+2*k n : ℕ) : ℝ)/2+1) =
      (n : ℝ)/2+(k n : ℝ)+1 := by push_cast; ring
  rw [harg]
  ring

theorem realGinibreWeightedUpperExponent_eventual (k : ℕ → ℕ) (α : ℝ)
    (hα : 0 < α)
    (hk : Tendsto (fun n => (k n : ℝ)/(n : ℝ)) atTop (𝓝 α))
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (realGinibreWeightedUpperExponent n (k n)) ≤
        Real.exp ((n : ℝ)*(powerRate 1 α+δ)) := by
  have ht := realGinibreWeightedUpperExponent_rate k α hα hk
  filter_upwards [(tendsto_order.mp ht).2 (powerRate 1 α+δ) (by linarith),
    eventually_gt_atTop 0] with n hn hn0
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  apply Real.exp_le_exp.mpr
  simpa only [mul_comm] using ((div_lt_iff₀ hnR).mp hn).le

#print axioms realGinibreWeightedUpperExponent_rate
#print axioms realGinibreWeightedUpperExponent_eventual
end SpectralRadiusUpperTail
