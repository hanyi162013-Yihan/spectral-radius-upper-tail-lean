import SpectralRadiusUpperTail.DyadicMomentOrder
import SpectralRadiusUpperTail.PowerRatioSmallness

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

lemma dyadicMomentOrder_ratio_tendsto (p d : ℕ) (hpd : p < d) :
    Tendsto (fun n : ℕ => (dyadicMomentOrder d n : ℝ)^p/(n : ℝ)) atTop (𝓝 0) := by
  apply power_div_dimension_tendsto (dyadicMomentOrder_tendsto d (by omega)) p d hpd ((2 : ℝ)^d)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact_mod_cast dyadicOrder_pow_le_dimension d n (by omega)

lemma dyadicMomentOrder_tail_tendsto (d : ℕ) (hd : 0 < d)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    Tendsto (fun n : ℕ => (n : ℝ)*a^(dyadicMomentOrder d n)) atTop (𝓝 0) := by
  apply dimension_mul_geometric_tendsto (dyadicMomentOrder_tendsto d hd) d _ a ha ha1
  exact Eventually.of_forall (fun n => by exact_mod_cast (dimension_lt_dyadicOrder_pow d hd n).le)

#print axioms dyadicMomentOrder_ratio_tendsto
#print axioms dyadicMomentOrder_tail_tendsto
end SpectralRadiusUpperTail
