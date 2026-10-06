import SpectralRadiusUpperTail.MarkedNonrealCoordinates
import SpectralRadiusUpperTail.RealSchurMixedDiagonalProductIntegral
import SpectralRadiusUpperTail.RealSchurMixedFlagGaussianFactors

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix ENNReal

noncomputable def markedNonrealDiagonalSplit (m : ℕ) :
    (RealSchurMixedDiagonalEntry (markedNonrealBlockSizes m) → ℝ) ≃ᵐ
      (((Fin 2 × Fin 2) → ℝ) × ((Fin m × Fin m) → ℝ)) :=
  (realSchurMixedDiagonalProductEquiv (markedNonrealBlockSizes m)).trans
    (MeasurableEquiv.piFinTwo (fun i =>
      (Fin (markedNonrealBlockSizes m i) × Fin (markedNonrealBlockSizes m i)) → ℝ))

theorem markedNonrealDiagonalSplit_measurePreserving (m : ℕ) :
    MeasurePreserving (markedNonrealDiagonalSplit m) :=
  (volume_preserving_piFinTwo _).comp (realSchurMixedDiagonalProductEquiv_measurePreserving _)

theorem markedNonrealDiagonalSplit_first (m : ℕ)
    (d : RealSchurMixedDiagonalEntry (markedNonrealBlockSizes m) → ℝ)
    (u : RealSchurMixedStrictUpperEntry (markedNonrealBlockSizes m) → ℝ) :
    markedNonrealFirstBlock m (realSchurMixedUpperEntryJoin (markedNonrealBlockSizes m) d u) =
      Matrix.of (markedNonrealDiagonalSplit m d).1.curry :=
  realSchurMixedDiagonalProductEquiv_nativeBlock _ d u 0

theorem markedNonrealDiagonalSplit_second (m : ℕ)
    (d : RealSchurMixedDiagonalEntry (markedNonrealBlockSizes m) → ℝ)
    (u : RealSchurMixedStrictUpperEntry (markedNonrealBlockSizes m) → ℝ) :
    markedNonrealComplement m (realSchurMixedUpperEntryJoin (markedNonrealBlockSizes m) d u) =
      Matrix.of (markedNonrealDiagonalSplit m d).2.curry :=
  realSchurMixedDiagonalProductEquiv_nativeBlock _ d u 1

theorem markedNonrealDiagonal_gaussian_factor (m : ℕ)
    (d : RealSchurMixedDiagonalEntry (markedNonrealBlockSizes m) → ℝ) :
    Real.exp (-(∑ p : RealSchurMixedDiagonalEntry (markedNonrealBlockSizes m), (d p)^2)/2) =
      realMatrixGaussianWeight (Fin 2) (Matrix.of (markedNonrealDiagonalSplit m d).1.curry)*
        realMatrixGaussianWeight (Fin m) (Matrix.of (markedNonrealDiagonalSplit m d).2.curry) := by
  rw [realSchurMixedDiagonal_gaussian_product,Fin.prod_univ_two]
  rfl

theorem markedNonrealDiagonalJacobian_factor (m : ℕ)
    (d : RealSchurMixedDiagonalEntry (markedNonrealBlockSizes m) → ℝ) :
    realSchurMixedDiagonalGaussianJacobian (markedNonrealBlockSizes m) d =
      |(realSchurRectangularSylvester (Matrix.of (markedNonrealDiagonalSplit m d).2.curry)
        (Matrix.of (markedNonrealDiagonalSplit m d).1.curry)).det| *
      (realMatrixGaussianWeight (Fin 2) (Matrix.of (markedNonrealDiagonalSplit m d).1.curry)*
        realMatrixGaussianWeight (Fin m) (Matrix.of (markedNonrealDiagonalSplit m d).2.curry)) := by
  letI : Unique (RealSchurLowerIndex 2) :=
    { default := markedRealLowerIndex, uniq := markedRealLowerIndex_unique }
  rw [realSchurMixedDiagonalGaussianJacobian,Fintype.prod_unique,
    realSchurMixedSylvester_eq_diagonalMatrix,markedNonrealDiagonal_gaussian_factor]
  congr 2

#print axioms markedNonrealDiagonalSplit_measurePreserving
#print axioms markedNonrealDiagonalSplit_first
#print axioms markedNonrealDiagonalSplit_second
#print axioms markedNonrealDiagonal_gaussian_factor
#print axioms markedNonrealDiagonalJacobian_factor
end SpectralRadiusUpperTail
