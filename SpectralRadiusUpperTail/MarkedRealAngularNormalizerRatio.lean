import SpectralRadiusUpperTail.MarkedRealAngularExteriorCountLower
import SpectralRadiusUpperTail.MarkedRealEigenlineBasis
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped ENNReal

/-- After integrating the free row and complementary matrix, the
remaining Gaussian partition function is exactly one column's worth. -/
theorem markedRealAngular_gaussianNormalizer_ratio (m : ℕ) :
    ENNReal.ofReal ((Real.sqrt (2*Real.pi))^(m^2+m)) *
      (ENNReal.ofReal ((Real.sqrt (2*Real.pi))^
        ((Fintype.card
          (RealSchurMixedCoord (markedRealTwoBlockSizes m)))^2)))⁻¹ =
      (ENNReal.ofReal ((Real.sqrt (2*Real.pi))^(m+1)))⁻¹ := by
  let c : ℝ := Real.sqrt (2*Real.pi)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hp : (m+1)^2 = (m^2+m)+(m+1) := by ring
  have hq : ENNReal.ofReal (c^((m+1)^2)) =
      ENNReal.ofReal (c^(m^2+m)) * ENNReal.ofReal (c^(m+1)) := by
    rw [hp, pow_add, ENNReal.ofReal_mul (pow_nonneg hc.le _)]
  rw [markedRealTwoBlock_card]
  change ENNReal.ofReal (c^(m^2+m)) *
      (ENNReal.ofReal (c^((m+1)^2)))⁻¹ =
      (ENNReal.ofReal (c^(m+1)))⁻¹
  have hzero : ENNReal.ofReal (c^(m^2+m)) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hc _))
  have htop : ENNReal.ofReal (c^(m^2+m)) ≠ ∞ := by simp
  rw [hq, ENNReal.mul_inv (Or.inl hzero) (Or.inl htop)]
  exact ENNReal.mul_inv_cancel_left hzero htop

#print axioms markedRealAngular_gaussianNormalizer_ratio
end SpectralRadiusUpperTail
