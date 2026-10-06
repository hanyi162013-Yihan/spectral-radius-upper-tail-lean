import SpectralRadiusUpperTail.RealGaussianPositiveCountFormula
import SpectralRadiusUpperTail.RealGaussianRadiusMarkedLineConditional

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- Sharp exponential rate for the actual expected number of positive
real exterior eigenvalues, without a one-point formula assumption. -/
theorem realGaussian_positiveCount_log_rate (r : ℝ) (hr : 1 < r) :
    Tendsto (fun n : ℕ => Real.log
      (∫ a, realGaussianExteriorCount n r 0 a ∂gaussianMatrixLaw n)/(n : ℝ))
      atTop (𝓝 (-rate 1 r)) := by
  apply (gaussianMarkedRealTailMass_log_rate r hr).congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  rw [realGaussian_positiveCount_eq_markedRealTailMass n hn r hr]

/-- In the independent real-Gaussian radius proof, the real one-point
identity has been discharged. Only the nonreal count upper bound remains
as a finite-dimensional intensity input. The conditional Schur power
transfer is a separate main-theorem interface. -/
theorem realGaussianRadius_rate_of_nonreal_count
    (r : ℝ) (hr : 1 < r)
    (hNonreal : ∀ n, 3 ≤ n →
      (∫ x, realGaussianExteriorCount n r 2 x ∂gaussianMatrixLaw n) ≤
        2*realGinibreNonrealExteriorMass n r) :
    Tendsto (fun n : ℕ => Real.log ((gaussianMatrixLaw n).real
      {x | r < realMatrixRadius ((1/Real.sqrt (n : ℝ)) • entryMatrix x)})/(n : ℝ))
      atTop (𝓝 (-rate 1 r)) :=
  realGaussianRadius_rate_of_marked_line_and_nonreal_count r hr
    (fun n hn => realGaussian_positiveCount_eq_markedRealTailMass n (by omega) r hr)
    hNonreal

#print axioms realGaussian_positiveCount_log_rate
#print axioms realGaussianRadius_rate_of_nonreal_count
end SpectralRadiusUpperTail
