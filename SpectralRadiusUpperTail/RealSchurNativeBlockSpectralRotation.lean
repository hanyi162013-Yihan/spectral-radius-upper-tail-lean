import SpectralRadiusUpperTail.RealSchurNativeBlockRotation
import SpectralRadiusUpperTail.RealSchurAtomicDiagonalSpectralDependence

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

theorem realSchurMixedDiagonalConjugation_native_charpoly
    {m : ℕ} (s : Fin m → ℕ)
    (Q : (i : Fin m) → Matrix (Fin (s i)) (Fin (s i)) ℝ) (hQ : ∀ i, (Q i)ᵀ*Q i=1)
    (d : RealSchurMixedDiagonalEntry s → ℝ) (i : Fin m) :
    (realSchurMixedDiagonalMatrix s (realSchurMixedUpperEntryJoin s
      (realSchurMixedDiagonalConjugation s (Matrix.blockDiagonal' Q) d) 0) i).charpoly =
      (realSchurMixedDiagonalMatrix s (realSchurMixedUpperEntryJoin s d 0) i).charpoly := by
  rw [realSchurMixedDiagonalProductEquiv_nativeBlock,realSchurMixedDiagonalProductEquiv_nativeBlock,
    realSchurMixedDiagonalProduct_conjugation]
  exact realMatrixOrthogonalConjugation_charpoly _ _ _ (hQ i)

theorem realSchurAtomicDiagonalSource_block_rotation
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool)
    (Q : (i : Fin m) → Matrix (Fin (s i)) (Fin (s i)) ℝ) (hQ : ∀ i, (Q i)ᵀ*Q i=1)
    (d : RealSchurMixedDiagonalEntry s → ℝ) :
    realSchurMixedDiagonalConjugation s (Matrix.blockDiagonal' Q) d ∈ realSchurAtomicDiagonalSource s code ↔
      d ∈ realSchurAtomicDiagonalSource s code :=
  realSchurAtomicDiagonalSource_iff_of_polynomials s hs code _ _
    (realSchurMixedDiagonalConjugation_native_charpoly s Q hQ d)

theorem realSchurMixedDiagonalGapWeight_block_rotation
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, s i=1 ∨ s i=2)
    (Q : (i : Fin m) → Matrix (Fin (s i)) (Fin (s i)) ℝ) (hQ : ∀ i, (Q i)ᵀ*Q i=1)
    (d : RealSchurMixedDiagonalEntry s → ℝ) :
    realSchurMixedDiagonalGapWeight s (realSchurMixedDiagonalConjugation s (Matrix.blockDiagonal' Q) d)=
      realSchurMixedDiagonalGapWeight s d :=
  realSchurMixedDiagonalGapWeight_eq_of_polynomials s hs _ _
    (realSchurMixedDiagonalConjugation_native_charpoly s Q hQ d)

#print axioms realSchurMixedDiagonalConjugation_native_charpoly
#print axioms realSchurAtomicDiagonalSource_block_rotation
#print axioms realSchurMixedDiagonalGapWeight_block_rotation
end SpectralRadiusUpperTail
