import SpectralRadiusUpperTail.RealGaussianPositivePowerIntensity
import SpectralRadiusUpperTail.RealGaussianRealIntensityDensity
import SpectralRadiusUpperTail.GaussianMarkedRealWeightedIntegrable

namespace SpectralRadiusUpperTail
open MeasureTheory Set Classical
open scoped ENNReal

/-- The actual positive real-root statistic has the same weighted
one-point density as the unweighted count. The power may be arbitrarily
large; integrability is proved, not assumed. -/
theorem realGaussianPositivePower_eq_weighted_density_succ
    (m k : ℕ) (hm : 0 < m) :
    (∫ a, realGaussianPositiveRealExteriorPower (m+1) k a
      ∂gaussianMatrixLaw (m+1)) =
      ∫ x : ℝ in Ioi 1, x^(2*k)*gaussianMarkedRealDensity (m+1) x := by
  have hleft : 0 ≤ ∫ a, realGaussianPositiveRealExteriorPower (m+1) k a
      ∂gaussianMatrixLaw (m+1) :=
    integral_nonneg (fun a => (matrixPositiveRealExteriorPower_nonneg_le_total _ k).1)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (1 : ℝ))]
      (fun x => x^(2*k)*gaussianMarkedRealDensity (m+1) x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (gaussianMarkedRealDensity_weighted_bounds (m+1) k (by omega) x hx.le).1
  have hright : 0 ≤ ∫ x : ℝ in Ioi 1,
      x^(2*k)*gaussianMarkedRealDensity (m+1) x := integral_nonneg_of_ae hnonneg
  have hw : Measurable (fun x : ℝ =>
      if 1 < x then ENNReal.ofReal (x^(2*k)) else 0) := by
    change Measurable ((Ioi (1 : ℝ)).indicator
      (fun x : ℝ => ENNReal.ofReal (x^(2*k))))
    exact (by fun_prop : Measurable (fun x : ℝ =>
      ENNReal.ofReal (x^(2*k)))).indicator measurableSet_Ioi
  apply (ENNReal.ofReal_eq_ofReal_iff hleft hright).mp
  rw [realGaussianPositivePower_ofReal_eq_intensity (m+1) k (by omega),
    realGaussianRealIntensity_lintegral_density m hm _ hw,
    ofReal_integral_eq_lintegral_ofReal
      (gaussianMarkedRealDensity_weighted_integrableOn (m+1) k (by omega)) hnonneg,
    ← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro x
  by_cases hx : 1 < x
  · rw [if_pos hx, indicator_of_mem (show x ∈ Ioi (1 : ℝ) from hx),
      gaussianMarkedRealScaledWeight_eq_exterior_density m x (by linarith),
      ENNReal.ofReal_mul (pow_nonneg (by linarith : 0 ≤ x) _)]
    exact mul_comm _ _
  · simp [hx]

theorem realGaussianPositivePower_eq_weighted_density
    (n k : ℕ) (hn : 2 ≤ n) :
    (∫ a, realGaussianPositiveRealExteriorPower n k a ∂gaussianMatrixLaw n) =
      ∫ x : ℝ in Ioi 1, x^(2*k)*gaussianMarkedRealDensity n x := by
  cases n with
  | zero => omega
  | succ m => exact realGaussianPositivePower_eq_weighted_density_succ m k (by omega)

#print axioms realGaussianPositivePower_eq_weighted_density_succ
#print axioms realGaussianPositivePower_eq_weighted_density
end SpectralRadiusUpperTail
