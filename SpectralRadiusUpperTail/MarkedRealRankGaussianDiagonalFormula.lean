import SpectralRadiusUpperTail.MarkedRealRankGaussianFactor
import SpectralRadiusUpperTail.MarkedRealRankRestIntegral
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix

/-- On each real-root rank, the actual matrix Gaussian area integral is
an angular mass times an integral only over the scalar and complementary
matrix. The free upper row is completely integrated out. -/
theorem markedRealAngularRank_gaussian_diagonal_formula
    (m k : ℕ) (hm : 0 < m) (b : ℝ) :
    (∫⁻ y in
      realSchurMixedEntryCoordinates (markedRealTwoBlockSizes m) 0 ''
        (markedRealAngularPositiveSource m ×ˢ
          markedRealUpperRankSource m k b),
      ENNReal.ofReal
        (realSchurMixedGaussianCoordinateWeight
          (markedRealTwoBlockSizes m) y)
        ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m)) =
      (∫⁻ ω, markedRealAngularWeight m ω) *
        (∫⁻ d, markedRealRankDiagonalWeight m k b d) := by
  rw [markedRealAngularRank_gaussian_factor m k hm b,
    markedRealRankRestWeight_lintegral_diagonal m k hm b]

#print axioms markedRealAngularRank_gaussian_diagonal_formula
end SpectralRadiusUpperTail
