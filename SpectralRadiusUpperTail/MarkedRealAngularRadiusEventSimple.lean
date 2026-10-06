import SpectralRadiusUpperTail.MarkedRealAngularLocalCountSimple
import SpectralRadiusUpperTail.MarkedRealAngularRadiusEventLower
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set
open scoped ENNReal Matrix

/-- An actual-law finite-dimensional Gaussian spectral-radius lower
bound in which only one Gaussian first-column normalizer remains. -/
theorem markedRealAngular_gaussianRadiusEvent_lower_simple
    (m : ℕ) (hm : 0 < m) (r : ℝ) :
    (∫⁻ ω, markedRealAngularWeight m ω) *
        (∫⁻ x : ℝ,
          if r * Real.sqrt ((m+1 : ℕ) : ℝ) < x then
            ENNReal.ofReal (Real.exp (-x^2/2)) *
              markedRealGaussianCharpolyMoment m x
          else 0) *
        (ENNReal.ofReal ((Real.sqrt (2*Real.pi))^(m+1)))⁻¹ ≤
      (m+1 : ℝ≥0∞) *
        gaussianMatrixLaw (m+1)
          {a : (Fin (m+1) × Fin (m+1)) → ℝ |
            r < realMatrixRadius
              ((1/Real.sqrt ((m+1 : ℕ) : ℝ)) • entryMatrix a)} := by
  rw [← markedRealAngularLocalCountLower_simple]
  exact markedRealAngularLocalCountLower_le_radiusEvent m hm r

#print axioms markedRealAngular_gaussianRadiusEvent_lower_simple
end SpectralRadiusUpperTail
