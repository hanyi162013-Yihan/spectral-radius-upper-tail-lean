import SpectralRadiusUpperTail.GaussianMarkedRealSphereArea
import SpectralRadiusUpperTail.MarkedRealGaussianBlockWeight
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- The full iid Gaussian normalizer splits into the free upper row,
the complementary matrix, and the constrained first column. -/
theorem markedRealGaussianNormalizer_split (m : ℕ) :
    (Real.sqrt (2*Real.pi))^((m+1)^2) =
      (Real.sqrt (2*Real.pi))^m *
        (Real.sqrt (2*Real.pi))^(m*m) *
        (Real.sqrt (2*Real.pi))^(m+1) := by
  rw [← pow_add, ← pow_add]
  congr 1
  ring

/-- Dividing the sphere area by the two unit eigenvector marks and by
the Gaussian density of the constrained first column yields the exact
real-eigenvalue Kac--Rice coefficient. -/
theorem markedRealSphere_gaussianColumnCoefficient
    (n : ℕ) (hn : 0 < n) :
    ((2 * (Real.sqrt Real.pi)^n /
      Real.Gamma ((n : ℝ)/2)) / 2) /
        (Real.sqrt (2*Real.pi))^n =
      (2 : ℝ)^(-((n : ℝ)/2)) /
        Real.Gamma ((n : ℝ)/2) := by
  have hpi : 0 < Real.sqrt Real.pi := by positivity
  have htwo : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hG : 0 < Real.Gamma ((n : ℝ)/2) :=
    Real.Gamma_pos_of_pos (by positivity)
  have hsqrt : Real.sqrt (2*Real.pi) =
      Real.sqrt (2 : ℝ) * Real.sqrt Real.pi := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2)]
  have hpow : (Real.sqrt (2 : ℝ))^n =
      (2 : ℝ)^((n : ℝ)/2) := by
    rw [← Real.rpow_natCast]
    exact (Real.rpow_div_two_eq_sqrt (n : ℝ)
      (by positivity : (0 : ℝ) ≤ 2)).symm
  rw [hsqrt, mul_pow, hpow, Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2)]
  field_simp [hpi.ne', htwo.ne', hG.ne',
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) ((n : ℝ)/2)).ne']

#print axioms markedRealGaussianNormalizer_split
#print axioms markedRealSphere_gaussianColumnCoefficient
end SpectralRadiusUpperTail
