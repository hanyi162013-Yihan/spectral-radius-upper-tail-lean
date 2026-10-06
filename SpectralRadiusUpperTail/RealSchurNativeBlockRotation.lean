import SpectralRadiusUpperTail.RealSchurMixedDiagonalProductIntegral
import SpectralRadiusUpperTail.RealSchurBlockUpperConjugation

namespace SpectralRadiusUpperTail
open scoped Matrix

theorem realSchurMixed_blockDiagonal_off
    {m : ℕ} (s : Fin m → ℕ) (Q : (i : Fin m) → Matrix (Fin (s i)) (Fin (s i)) ℝ)
    (i j : RealSchurMixedCoord s) (h : i.1 ≠ j.1) :
    Matrix.blockDiagonal' Q i j=0 := by
  exact Matrix.blockDiagonal'_apply_ne Q i.2 j.2 h

theorem realSchurMixed_blockDiagonal_orthogonal
    {m : ℕ} (s : Fin m → ℕ) (Q : (i : Fin m) → Matrix (Fin (s i)) (Fin (s i)) ℝ)
    (hQ : ∀ i, (Q i)ᵀ*Q i=1) :
    (Matrix.blockDiagonal' Q)ᵀ*Matrix.blockDiagonal' Q=1 := by
  rw [Matrix.blockDiagonal'_transpose,← Matrix.blockDiagonal'_mul]
  simp only [hQ]
  exact Matrix.blockDiagonal'_one

theorem realSchurMixedDiagonalJoin_eq_blockDiagonal
    {m : ℕ} (s : Fin m → ℕ) (d : RealSchurMixedDiagonalEntry s → ℝ) :
    realSchurMixedUpperEntryJoin s d 0 =
      Matrix.blockDiagonal' (fun i => Matrix.of (realSchurMixedDiagonalProductEquiv s d i).curry) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  by_cases hij : i=j
  · subst j
    simp [realSchurMixedUpperEntryJoin,Matrix.blockDiagonal'_apply_eq,
      realSchurMixedDiagonalProductEquiv_apply]
  · simp [realSchurMixedUpperEntryJoin,hij,Matrix.blockDiagonal'_apply_ne _ _ _ hij]

/-- The diagonal action induced by a block-diagonal matrix is exactly
the separate conjugation of each native block entry array. -/
theorem realSchurMixedDiagonalProduct_conjugation
    {m : ℕ} (s : Fin m → ℕ) (Q : (i : Fin m) → Matrix (Fin (s i)) (Fin (s i)) ℝ)
    (d : RealSchurMixedDiagonalEntry s → ℝ) (i : Fin m) :
    Matrix.of (realSchurMixedDiagonalProductEquiv s
      (realSchurMixedDiagonalConjugation s (Matrix.blockDiagonal' Q) d) i).curry =
        Q i*Matrix.of (realSchurMixedDiagonalProductEquiv s d i).curry*(Q i)ᵀ := by
  have he := realSchurMixedDiagonalConjugation_embed s (Matrix.blockDiagonal' Q)
    (realSchurMixed_blockDiagonal_off s Q) d
  rw [realSchurMixedDiagonalJoin_eq_blockDiagonal,
    realSchurMixedDiagonalJoin_eq_blockDiagonal,Matrix.blockDiagonal'_transpose,
    ← Matrix.blockDiagonal'_mul,← Matrix.blockDiagonal'_mul] at he
  ext a b
  have hh := congrArg (fun T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ =>
    T ⟨i,a⟩ ⟨i,b⟩) he
  simpa only [Matrix.blockDiagonal'_apply_eq] using hh

#print axioms realSchurMixed_blockDiagonal_off
#print axioms realSchurMixed_blockDiagonal_orthogonal
#print axioms realSchurMixedDiagonalJoin_eq_blockDiagonal
#print axioms realSchurMixedDiagonalProduct_conjugation
end SpectralRadiusUpperTail
