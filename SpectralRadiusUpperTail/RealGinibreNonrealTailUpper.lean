import SpectralRadiusUpperTail.RealGinibreNonrealDensityAt
import SpectralRadiusUpperTail.PlanarPoissonIntegrable
import SpectralRadiusUpperTail.PlanarPoissonTailUpper
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set Metric

theorem realGinibreNonrealDensityAt_integrableOn (n : ℕ) (r : ℝ)
    (hr : 1 < r) (hnpos : 0 < n)
    (hn : 1/r ≤ (n : ℝ)*(r-1/r)) :
    IntegrableOn (realGinibreNonrealDensityAt n) {z : ℂ | r < ‖z‖} := by
  have hbase := (planarPoisson_integrableOn n r hr hnpos hn).const_mul
    ((n : ℝ)/Real.pi)
  apply hbase.mono' (realGinibreNonrealDensityAt_measurable n).aestronglyMeasurable
  have hset : MeasurableSet {z : ℂ | r < ‖z‖} :=
    measurableSet_lt measurable_const measurable_norm
  filter_upwards [ae_restrict_mem hset] with z hz
  have hb := realGinibreNonrealDensityAt_bound n z
    (by linarith [show r < ‖z‖ from hz])
  have hrhs : 0 ≤ (n : ℝ)/Real.pi *
      Real.exp (-(n : ℝ)*rate 2 ‖z‖) := by positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1,
    abs_of_nonneg hrhs] using hb.2

/-- The integrated nonreal real-Ginibre one-point expression is at most
the planar Poisson envelope. -/
theorem realGinibreNonrealTailUpper (n : ℕ) (r : ℝ)
    (hr : 1 < r) (hnpos : 0 < n)
    (hn : 1/r ≤ (n : ℝ)*(r-1/r)) :
    (∫ z : ℂ in {z | r < ‖z‖}, realGinibreNonrealDensityAt n z) ≤
      (n : ℝ)/Real.pi *
        (2 * (volume : Measure ℂ).real (ball 0 1) *
          ((r * Real.exp (-(n : ℝ)*rate 2 r)) /
            ((n : ℝ)*(r-1/r)))) := by
  have hset : MeasurableSet {z : ℂ | r < ‖z‖} :=
    measurableSet_lt measurable_const measurable_norm
  have hfirst := setIntegral_mono_on
    (realGinibreNonrealDensityAt_integrableOn n r hr hnpos hn)
    ((planarPoisson_integrableOn n r hr hnpos hn).const_mul
      ((n : ℝ)/Real.pi)) hset
    (fun z hz => (realGinibreNonrealDensityAt_bound n z
      (by linarith [show r < ‖z‖ from hz])).2)
  rw [integral_const_mul] at hfirst
  calc
    _ ≤ (n : ℝ)/Real.pi *
        (∫ z : ℂ in {z | r < ‖z‖},
          Real.exp (-(n : ℝ)*rate 2 ‖z‖)) := hfirst
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (planarPoissonTailUpper n r hr hnpos hn) (by positivity)

#print axioms realGinibreNonrealDensityAt_integrableOn
#print axioms realGinibreNonrealTailUpper
end SpectralRadiusUpperTail
