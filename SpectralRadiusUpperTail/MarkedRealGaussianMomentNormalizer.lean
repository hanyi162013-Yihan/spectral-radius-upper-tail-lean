import SpectralRadiusUpperTail.MarkedRealUpperRowDimension
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped ENNReal

/-- The free upper row and complementary matrix contribute exactly
m + m² unnormalized Gaussian coordinates. -/
theorem markedRealTwoBlock_gaussianNormalizer_product (m : ℕ) :
    ENNReal.ofReal ((Real.sqrt (2*Real.pi)) ^
      (Fintype.card
        (RealSchurMixedStrictUpperEntry (markedRealTwoBlockSizes m)))) *
      ENNReal.ofReal ((Real.sqrt (2*Real.pi))^(m^2)) =
        ENNReal.ofReal ((Real.sqrt (2*Real.pi))^(m + m^2)) := by
  rw [markedRealTwoBlock_strictUpper_card]
  rw [← ENNReal.ofReal_mul
    (pow_nonneg (Real.sqrt_nonneg _) _)]
  rw [← pow_add]

#print axioms markedRealTwoBlock_gaussianNormalizer_product
end SpectralRadiusUpperTail
