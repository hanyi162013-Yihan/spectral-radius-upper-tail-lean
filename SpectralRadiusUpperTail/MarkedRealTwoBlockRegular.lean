import SpectralRadiusUpperTail.MarkedRealEigenlineBlockUpper
import SpectralRadiusUpperTail.MarkedRealTwoBlockGaussianChart
import SpectralRadiusUpperTail.RealSchurMixedSeparatedBlocks
import SpectralRadiusUpperTail.RealSchurMixedNativeDiagonal
import SpectralRadiusUpperTail.RealSchurScalarPairCoprime
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix
open Polynomial

/-- If the full two-block matrix has simple characteristic spectrum, its
marked scalar eigenvalue is separated from the complementary block. -/
theorem markedRealTwoBlock_complement_det_ne_zero
    (m : ℕ) (hm : 0 < m)
    (T : Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
      (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ)
    (hT : realSchurMixedLowerProjection (markedRealTwoBlockSizes m) T = 0)
    (hsep : T.charpoly.Separable) :
    (markedRealComplement m T - markedRealScalar m T •
      (1 : Matrix (Fin m) (Fin m) ℝ)).det ≠ 0 := by
  let s := markedRealTwoBlockSizes m
  let x := markedRealScalar m T
  let H := markedRealComplement m T
  have hs : ∀ i : Fin 2, 0 < s i := by
    intro i
    fin_cases i <;> simp [s, markedRealTwoBlockSizes, hm]
  have hpair := realSchurMixed_blockUpper_charpoly_pairwise_coprime s hs T hT hsep
  have h0 : realSchurMixedDiagonalMatrix s T 0 = Matrix.scalar (Fin 1) x := by
    ext i j
    fin_cases i
    fin_cases j
    simp [realSchurMixedDiagonalMatrix, Matrix.scalar_apply, s,
      markedRealTwoBlockSizes, x, markedRealScalar, markedRealZeroCoordinate]
  have h1 : realSchurMixedDiagonalMatrix s T 1 = H := by
    rfl
  have hcop : IsCoprime (Matrix.scalar (Fin 1) x).charpoly H.charpoly := by
    have h := hpair (show (0 : Fin 2) ≠ 1 by decide)
    change IsCoprime
      (T.toSquareBlock (fun z : RealSchurMixedCoord s => z.1) 0).charpoly
      (T.toSquareBlock (fun z : RealSchurMixedCoord s => z.1) 1).charpoly at h
    rw [realSchurMixedDiagonalMatrix_charpoly,
      realSchurMixedDiagonalMatrix_charpoly, h0, h1] at h
    exact h
  have heval : H.charpoly.eval x ≠ 0 := by
    rcases aeval_ne_zero_of_isCoprime hcop x with h | h
    · rw [realSchurScalar_charpoly] at h
      simp at h
    · simpa using h
  have hscalar : Matrix.scalar (Fin m) x =
      x • (1 : Matrix (Fin m) (Fin m) ℝ) := by
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply,
      Matrix.smul_apply, Matrix.one_apply]
  have hdet : (x • (1 : Matrix (Fin m) (Fin m) ℝ) - H).det ≠ 0 := by
    simpa only [Matrix.eval_charpoly, hscalar] using heval
  have hneg : H - x • (1 : Matrix (Fin m) (Fin m) ℝ) =
      -(x • (1 : Matrix (Fin m) (Fin m) ℝ) - H) := by
    abel
  rw [hneg, Matrix.det_neg]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hdet

/-- Every simple-spectrum marked real eigenline is a nonsingular center
for the two-block Schur chart. -/
theorem markedRealTwoBlock_orbit_det_ne_zero
    (m : ℕ) (hm : 0 < m)
    (T : Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
      (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ)
    (hT : realSchurMixedLowerProjection (markedRealTwoBlockSizes m) T = 0)
    (hsep : T.charpoly.Separable) :
    (realSchurMixedOrbitMatrix (markedRealTwoBlockSizes m) T).det ≠ 0 := by
  rw [markedRealOrbitMatrix_det m T
    (markedRealComplement m T) (markedRealScalar m T)
    (by intros; rfl) rfl]
  exact markedRealTwoBlock_complement_det_ne_zero m hm T hT hsep

#print axioms markedRealTwoBlock_complement_det_ne_zero
#print axioms markedRealTwoBlock_orbit_det_ne_zero
end SpectralRadiusUpperTail
