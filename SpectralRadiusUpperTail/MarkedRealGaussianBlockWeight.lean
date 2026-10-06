import SpectralRadiusUpperTail.MarkedRealTwoBlockGaussianChart
import SpectralRadiusUpperTail.RealSchurMixedUpperGaussianIntegral
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix BigOperators

/-- The Gaussian quadratic energy of a two-block upper matrix splits
into its scalar, upper row, and complementary matrix energies. -/
theorem markedRealUpper_sum_squares (m : ℕ)
    (S : Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
      (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ)
    (hS : realSchurMixedLowerProjection (markedRealTwoBlockSizes m) S = 0) :
    (∑ p : RealSchurMixedCoord (markedRealTwoBlockSizes m) ×
        RealSchurMixedCoord (markedRealTwoBlockSizes m),
      (S p.1 p.2)^2) =
      (markedRealScalar m S)^2 +
        (∑ i : Fin m,
          (S ⟨0, markedRealZeroCoordinate m⟩ ⟨1,i⟩)^2) +
      (∑ p : Fin m × Fin m, ((markedRealComplement m S) p.1 p.2)^2) := by
  have hzero (i : Fin m) :
      S ⟨1,i⟩ ⟨0,markedRealZeroCoordinate m⟩ = 0 := by
    have h := congrFun hS
      (⟨markedRealLowerIndex, (i, markedRealZeroCoordinate m)⟩ :
        RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m))
    change S ⟨1,i⟩ ⟨0,markedRealZeroCoordinate m⟩ = 0 at h
    exact h
  have hzero' (i : Fin m) : S ⟨1,i⟩ ⟨0,(0 : Fin 1)⟩ = 0 := hzero i
  simp only [Fintype.sum_prod_type]
  simp [Fintype.sum_sigma, Fin.sum_univ_two,
    markedRealTwoBlockSizes, markedRealScalar, markedRealComplement,
    markedRealZeroCoordinate, hzero', Finset.sum_add_distrib, add_assoc]

/-- On a block-upper Schur slice, the scalar, free upper row, and
complementary Gaussian factors are independent at the density level. -/
theorem markedRealUpper_gaussianWeight_factor (m : ℕ)
    (S : Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
      (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ)
    (hS : realSchurMixedLowerProjection (markedRealTwoBlockSizes m) S = 0) :
    realMatrixGaussianWeight (RealSchurMixedCoord (markedRealTwoBlockSizes m)) S =
      Real.exp (-(markedRealScalar m S)^2/2) *
        Real.exp (-(∑ i : Fin m,
          (S ⟨0,markedRealZeroCoordinate m⟩ ⟨1,i⟩)^2)/2) *
        realMatrixGaussianWeight (Fin m) (markedRealComplement m S) := by
  unfold realMatrixGaussianWeight
  rw [markedRealUpper_sum_squares m S hS]
  rw [show -((markedRealScalar m S)^2 +
      (∑ i : Fin m, (S ⟨0,markedRealZeroCoordinate m⟩ ⟨1,i⟩)^2) +
      (∑ p : Fin m × Fin m, ((markedRealComplement m S) p.1 p.2)^2))/2 =
      -(markedRealScalar m S)^2/2 -
      (∑ i : Fin m, (S ⟨0,markedRealZeroCoordinate m⟩ ⟨1,i⟩)^2)/2 -
      (∑ p : Fin m × Fin m, ((markedRealComplement m S) p.1 p.2)^2)/2 by ring]
  rw [sub_eq_add_neg, sub_eq_add_neg, Real.exp_add, Real.exp_add]
  ring

/-- Exact integral of the unrestricted Gaussian upper row in a marked
real Schur slice. -/
theorem integral_markedRealGaussianUpperRow (m : ℕ) :
    (∫ u : Fin m → ℝ,
      Real.exp (-(∑ i : Fin m, (u i)^2)/2)) =
        (Real.sqrt (2*Real.pi))^m := by
  simpa only [Fintype.card_fin] using
    realSchurMixedIndependentGaussianIntegral (Fin m)

#print axioms markedRealUpper_sum_squares
#print axioms markedRealUpper_gaussianWeight_factor
#print axioms integral_markedRealGaussianUpperRow
end SpectralRadiusUpperTail
