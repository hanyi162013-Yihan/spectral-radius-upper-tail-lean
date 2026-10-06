import SpectralRadiusUpperTail.RealSchurMixedChartCharpoly
import SpectralRadiusUpperTail.RealSchurMixedFullChart
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

/-- Orthogonal conjugation preserves the characteristic polynomial over
the real coefficient ring. -/
theorem realMatrixOrthogonalConjugation_charpoly
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (Q S : Matrix ι ι ℝ) (hQ : Qᵀ*Q=1) :
    (Q*S*Qᵀ).charpoly = S.charpoly := by
  rw [Matrix.charpoly_mul_comm]
  rw [← Matrix.mul_assoc Qᵀ Q S, hQ, Matrix.one_mul]

/-- At every parameter of a genuine mixed real-Schur local chart, the
characteristic polynomial is exactly the product of its current diagonal
block characteristic polynomials. -/
theorem realSchurMixedExpCoordinates_charpoly
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : realSchurMixedLowerProjection s T = 0)
    (x : RealSchurMixedTangent s) :
    (realSchurMixedExpCoordinates s T x).charpoly =
      ∏ i : Fin m,
        ((T+x.2.val).toSquareBlock
          (fun z : RealSchurMixedCoord s => z.1) i).charpoly := by
  rw [realSchurMixedExpCoordinates_eq_conjugation,
    realMatrixOrthogonalConjugation_charpoly _ _ _
      (realSchurMixedAngularFrame_orthogonal s x.1)]
  have hS : realSchurMixedLowerProjection s (T+x.2.val) = 0 := by
    rw [map_add, hT, zero_add]
    exact x.2.property
  exact realSchurMixed_blockUpper_charpoly s hs (T+x.2.val) hS

#print axioms realSchurMixedExpCoordinates_charpoly
end SpectralRadiusUpperTail
