import SpectralRadiusUpperTail.MarkedRealGaussianExpectationBridge
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator

/-- The actual iid real-Gaussian marked-root expectation is the global
countable Schur integral, divided by the exact Gaussian normalizer. This
still retains the patch restrictions and angular coordinates; it is not
yet the explicit one-point density. -/
theorem realGaussian_markedRootCount_global_area_formula
    (m : ℕ) (hm : 0 < m) (b : ℝ)
    (c : ℕ → RealSchurMixedRegularFrame (markedRealTwoBlockSizes m))
    (hcover :
      (⋃ k, markedRealIncidenceFirstPatch m b c k) = Set.univ) :
    (∫⁻ a : (Fin (m+1) × Fin (m+1)) → ℝ,
      markedRealSimpleRootCount m b
        (Matrix.reindex (markedRealIndexEquiv m)
          (markedRealIndexEquiv m) (Matrix.of a.curry))
        ∂gaussianMatrixLaw (m+1)) =
      (∑' k, ∫⁻ t in markedRealChartFirstSource m b c k,
        ENNReal.ofReal (
          |(markedRealComplement m ((c k).T+t.2.val) -
              markedRealScalar m ((c k).T+t.2.val) •
                (1 : Matrix (Fin m) (Fin m) ℝ)).det| *
            |realSchurMixedAngularJacobian (markedRealTwoBlockSizes m) t.1|) *
        ENNReal.ofReal (realMatrixGaussianWeight
          (RealSchurMixedCoord (markedRealTwoBlockSizes m))
            ((c k).T+t.2.val))
        ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m)) /
      ENNReal.ofReal
        ((Real.sqrt (2*Real.pi))^
          ((Fintype.card
            (RealSchurMixedCoord (markedRealTwoBlockSizes m)))^2)) := by
  let C : ℝ := (Real.sqrt (2*Real.pi))^
    ((Fintype.card (RealSchurMixedCoord (markedRealTwoBlockSizes m)))^2)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hfinite : ENNReal.ofReal C ≠ ∞ := by simp
  rw [realGaussian_markedRootCount_eq_mixedDensityIntegral]
  calc
    (∫⁻ y : RealSchurMixedTangent (markedRealTwoBlockSizes m),
      markedRealSimpleRootCount m b
        ((realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y) *
      ENNReal.ofReal
        (realSchurMixedGaussianCoordinateWeight
          (markedRealTwoBlockSizes m) y / C)
        ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m)) =
      ∫⁻ y,
        (markedRealSimpleRootCount m b
          ((realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y) *
        ENNReal.ofReal
          (realSchurMixedGaussianCoordinateWeight
            (markedRealTwoBlockSizes m) y)) *
        (ENNReal.ofReal C)⁻¹
        ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m) := by
      apply lintegral_congr
      intro y
      rw [ENNReal.ofReal_div_of_pos hC, div_eq_mul_inv, mul_assoc]
    _ = (∫⁻ y,
        markedRealSimpleRootCount m b
          ((realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y) *
        ENNReal.ofReal
          (realSchurMixedGaussianCoordinateWeight
            (markedRealTwoBlockSizes m) y)
          ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m)) *
        (ENNReal.ofReal C)⁻¹ := by
      exact lintegral_mul_const' _ _ (by simp [hC])
    _ = _ := by
      rw [markedReal_gaussian_global_area_formula m hm b c hcover]
      rw [div_eq_mul_inv]

#print axioms realGaussian_markedRootCount_global_area_formula
end SpectralRadiusUpperTail
