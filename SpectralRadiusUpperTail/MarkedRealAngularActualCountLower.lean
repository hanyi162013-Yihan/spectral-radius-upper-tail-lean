import SpectralRadiusUpperTail.MarkedRealAngularGaussianCountLower
import SpectralRadiusUpperTail.MarkedRealGaussianExpectationBridge
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix

/-- A fixed angular chart gives a fully normalized lower bound on the
expected number of positive real Gaussian eigenvalues above a cutoff. -/
theorem markedRealAngular_gaussianMoment_le_actualRootCount
    (m : ℕ) (hm : 0 < m) (b : ℝ) :
    ((∫⁻ ω, markedRealAngularWeight m ω) *
        (∫⁻ x : ℝ,
          if b < x then
            ENNReal.ofReal (Real.exp (-x^2/2)) *
              ENNReal.ofReal ((Real.sqrt (2*Real.pi))^(m^2+m)) *
              markedRealGaussianCharpolyMoment m x
          else 0)) *
        (ENNReal.ofReal ((Real.sqrt (2*Real.pi))^
          ((Fintype.card
            (RealSchurMixedCoord (markedRealTwoBlockSizes m)))^2)))⁻¹ ≤
      ∫⁻ a : (Fin (m+1) × Fin (m+1)) → ℝ,
        markedRealSimpleRootCount m b
          (Matrix.reindex (markedRealIndexEquiv m)
            (markedRealIndexEquiv m) (Matrix.of a.curry))
        ∂gaussianMatrixLaw (m+1) := by
  let C : ℝ := (Real.sqrt (2*Real.pi))^
    ((Fintype.card (RealSchurMixedCoord (markedRealTwoBlockSizes m)))^2)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hlocal := markedRealAngular_gaussianMoment_le_rootCountIntegral
    m hm b
  rw [realGaussian_markedRootCount_eq_mixedDensityIntegral]
  calc
    ((∫⁻ ω, markedRealAngularWeight m ω) *
        (∫⁻ x : ℝ,
          if b < x then
            ENNReal.ofReal (Real.exp (-x^2/2)) *
              ENNReal.ofReal ((Real.sqrt (2*Real.pi))^(m^2+m)) *
              markedRealGaussianCharpolyMoment m x
          else 0)) * (ENNReal.ofReal C)⁻¹ ≤
      (∫⁻ y,
        markedRealSimpleRootCount m b
          ((realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y) *
        ENNReal.ofReal
          (realSchurMixedGaussianCoordinateWeight
            (markedRealTwoBlockSizes m) y)
          ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m)) *
        (ENNReal.ofReal C)⁻¹ := by
      gcongr
    _ = ∫⁻ y,
        markedRealSimpleRootCount m b
          ((realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y) *
        ENNReal.ofReal
          (realSchurMixedGaussianCoordinateWeight
            (markedRealTwoBlockSizes m) y / C)
          ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m) := by
      rw [← lintegral_mul_const' _ _ (by simp [hC])]
      apply lintegral_congr
      intro y
      rw [ENNReal.ofReal_div_of_pos hC, div_eq_mul_inv, mul_assoc]

#print axioms markedRealAngular_gaussianMoment_le_actualRootCount
end SpectralRadiusUpperTail
