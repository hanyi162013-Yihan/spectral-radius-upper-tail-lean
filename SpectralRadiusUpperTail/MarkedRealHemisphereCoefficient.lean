import SpectralRadiusUpperTail.MarkedRealGaussianNormalization

namespace SpectralRadiusUpperTail
open scoped ENNReal

theorem markedRealHemisphere_gaussianColumnCoefficient
    (n : ℕ) (hn : 0 < n) :
    ((Real.sqrt Real.pi)^n / Real.Gamma ((n : ℝ)/2)) /
      (Real.sqrt (2*Real.pi))^n =
      (2 : ℝ)^(-((n : ℝ)/2)) / Real.Gamma ((n : ℝ)/2) := by
  have hh := markedRealSphere_gaussianColumnCoefficient n hn
  have he : (2 * (Real.sqrt Real.pi)^n / Real.Gamma ((n : ℝ)/2))/2 =
      (Real.sqrt Real.pi)^n / Real.Gamma ((n : ℝ)/2) := by ring
  rwa [he] at hh

theorem markedRealHemisphere_gaussianColumnCoefficient_ennreal
    (n : ℕ) (hn : 0 < n) :
    ENNReal.ofReal ((Real.sqrt Real.pi)^n / Real.Gamma ((n : ℝ)/2)) *
      (ENNReal.ofReal ((Real.sqrt (2*Real.pi))^n))⁻¹ =
      ENNReal.ofReal ((2 : ℝ)^(-((n : ℝ)/2)) / Real.Gamma ((n : ℝ)/2)) := by
  rw [← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos (by positivity),
    markedRealHemisphere_gaussianColumnCoefficient n hn]

#print axioms markedRealHemisphere_gaussianColumnCoefficient
#print axioms markedRealHemisphere_gaussianColumnCoefficient_ennreal
end SpectralRadiusUpperTail
