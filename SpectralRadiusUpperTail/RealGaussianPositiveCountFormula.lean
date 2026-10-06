import SpectralRadiusUpperTail.RealGaussianPositiveCountUnscaled
import SpectralRadiusUpperTail.PositiveScalarTailLIntegral
import SpectralRadiusUpperTail.GaussianMarkedRealAnalyticMass

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

theorem gaussianMarkedRealTailMass_ofReal (n : ℕ) (hn : 0 < n)
    (r : ℝ) (hr : 1 < r) :
    ENNReal.ofReal (gaussianMarkedRealTailMass n r) =
      ∫⁻ x in Set.Ioi r, ENNReal.ofReal (gaussianMarkedRealDensity n x) := by
  apply ofReal_integral_eq_lintegral_ofReal
    (gaussianMarkedRealDensity_integrableOn n hn r hr)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpos : 0 < x := by linarith [show r < x from hx]
  exact (realGinibreCoreDensity_pos n hn x hxpos).le.trans
    (gaussianMarkedRealDensity_sandwich n hn x (by linarith [show r < x from hx])).1

/-- The finite-dimensional real one-point tail identity is now proved
for the actual Gaussian matrix. It is no longer an external hypothesis. -/
theorem realGaussian_positiveCount_eq_markedRealTailMass_succ
    (m : ℕ) (hm : 0 < m) (r : ℝ) (hr : 1 < r) :
    (∫ a, realGaussianExteriorCount (m+1) r 0 a ∂gaussianMatrixLaw (m+1)) =
      gaussianMarkedRealTailMass (m+1) r := by
  have hleft : 0 ≤ ∫ a, realGaussianExteriorCount (m+1) r 0 a
      ∂gaussianMatrixLaw (m+1) :=
    integral_nonneg (fun a => (realGaussianExteriorCount_bounds (m+1) r 0 a).1)
  have hright := (gaussianMarkedRealTailMass_pos (m+1) (by omega) r hr).le
  apply (ENNReal.ofReal_eq_ofReal_iff hleft hright).mp
  rw [realGaussian_positiveCount_unscaled m hm r,
    gaussianMarkedRealTailMass_ofReal (m+1) (by omega) r hr,
    mul_comm r, positiveScalar_tail_lintegral _ r (by positivity)]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro x hx
  exact gaussianMarkedRealUnscaledWeight_rescale m x (by linarith [show r < x from hx])

theorem realGaussian_positiveCount_eq_markedRealTailMass
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (hr : 1 < r) :
    (∫ a, realGaussianExteriorCount n r 0 a ∂gaussianMatrixLaw n) =
      gaussianMarkedRealTailMass n r := by
  cases n with
  | zero => omega
  | succ m =>
    exact realGaussian_positiveCount_eq_markedRealTailMass_succ m (by omega) r hr

#print axioms gaussianMarkedRealTailMass_ofReal
#print axioms realGaussian_positiveCount_eq_markedRealTailMass_succ
#print axioms realGaussian_positiveCount_eq_markedRealTailMass
end SpectralRadiusUpperTail
