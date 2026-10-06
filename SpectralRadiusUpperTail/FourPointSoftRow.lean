import SpectralRadiusUpperTail.AtomicLaws
import SpectralRadiusUpperTail.SoftRow

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

instance fourPoint_isProbabilityMeasure : IsProbabilityMeasure fourPointMeasure := by
  constructor
  norm_num [fourPointMeasure, Measure.add_apply, Measure.smul_apply]
  calc
    (4 : ℝ≥0∞)⁻¹ + 4⁻¹ + 4⁻¹ + 4⁻¹ = 4 * (4 : ℝ≥0∞)⁻¹ := by ring
    _ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

/-- Equation (20) of the paper for the actual four-point probability measure. -/
theorem fourPoint_soft_integral_le (a t q : ℝ) (ha : 0 < a) :
    (∫ x : ℝ × ℝ, Real.exp (-((x.1-t)^2+(x.2-q)^2)/a) ∂fourPointMeasure)
      ≤ Real.exp (-(t^2+q^2)/(a+1)) := by
  apply planar_soft_integral_le fourPointMeasure a 1 t q ha (by norm_num)
  · intro u v
    exact fourPoint_integrable _
  · intro u v
    simpa using fourPoint_laplace u v

#print axioms fourPoint_isProbabilityMeasure
#print axioms fourPoint_soft_integral_le
end SpectralRadiusUpperTail
