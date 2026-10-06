import SpectralRadiusUpperTail.RealSchurMixedResultant
import SpectralRadiusUpperTail.RealSchurMixedNativeDiagonal
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

namespace SpectralRadiusUpperTail
open scoped Matrix

private theorem trace_eq_of_charpoly_eq {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) (h : A.charpoly=B.charpoly) : A.trace=B.trace := by
  rw [Matrix.trace_eq_neg_charpoly_nextCoeff,Matrix.trace_eq_neg_charpoly_nextCoeff,h]

private theorem det_eq_of_charpoly_eq {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) (h : A.charpoly=B.charpoly) : A.det=B.det := by
  rw [Matrix.det_eq_sign_charpoly_coeff,Matrix.det_eq_sign_charpoly_coeff,h]

private theorem one_eq_of_charpoly_eq
    (A B : Matrix (Fin 1) (Fin 1) ℝ) (h : A.charpoly=B.charpoly) : A=B := by
  have ht := trace_eq_of_charpoly_eq A B h
  have he : A 0 0=B 0 0 := by simpa [Matrix.trace,Fin.sum_univ_one] using ht
  ext i j
  fin_cases i <;> fin_cases j
  exact he

private theorem one_eq_scalar (A : Matrix (Fin 1) (Fin 1) ℝ) :
    A=Matrix.scalar (Fin 1) (A 0 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  simp

/-- Every scalar/pair Sylvester determinant is determined solely by
the characteristic polynomials of its two diagonal blocks. -/
theorem realSchurRectangularSylvester_det_eq_of_charpoly
    {a b : ℕ} (ha : a=1 ∨ a=2) (hb : b=1 ∨ b=2)
    (A A' : Matrix (Fin a) (Fin a) ℝ)
    (B B' : Matrix (Fin b) (Fin b) ℝ)
    (hA : A.charpoly=A'.charpoly) (hB : B.charpoly=B'.charpoly) :
    (realSchurRectangularSylvester A B).det=(realSchurRectangularSylvester A' B').det := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rw [one_eq_of_charpoly_eq A A' hA,one_eq_of_charpoly_eq B B' hB]
  · rw [one_eq_of_charpoly_eq A A' hA]
    conv_lhs => rw [one_eq_scalar A']
    conv_rhs => rw [one_eq_scalar A']
    rw [realSchurRectangularSylvester_scalar_pair_general,
      realSchurRectangularSylvester_scalar_pair_general,
      trace_eq_of_charpoly_eq B B' hB,det_eq_of_charpoly_eq B B' hB]
  · rw [one_eq_of_charpoly_eq B B' hB]
    conv_lhs => rw [one_eq_scalar B']
    conv_rhs => rw [one_eq_scalar B']
    rw [realSchurRectangularSylvester_pair_scalar_general,
      realSchurRectangularSylvester_pair_scalar_general,
      trace_eq_of_charpoly_eq A A' hA,det_eq_of_charpoly_eq A A' hA]
  · rw [realSchurRectangularSylvester_pair_pair_general,
      realSchurRectangularSylvester_pair_pair_general,
      trace_eq_of_charpoly_eq A A' hA,det_eq_of_charpoly_eq A A' hA,
      trace_eq_of_charpoly_eq B B' hB,det_eq_of_charpoly_eq B B' hB]

theorem realSchurMixedSylvester_det_eq_of_diagonal_charpoly
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, s i=1 ∨ s i=2)
    (A B : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (h : ∀ i, (realSchurMixedDiagonalMatrix s A i).charpoly=
      (realSchurMixedDiagonalMatrix s B i).charpoly)
    (p : RealSchurLowerIndex m) :
    (realSchurMixedSylvester s A p).det=(realSchurMixedSylvester s B p).det := by
  rw [realSchurMixedSylvester_eq_diagonalMatrix,realSchurMixedSylvester_eq_diagonalMatrix]
  exact realSchurRectangularSylvester_det_eq_of_charpoly (hs _) (hs _) _ _ _ _ (h _) (h _)

#print axioms realSchurRectangularSylvester_det_eq_of_charpoly
#print axioms realSchurMixedSylvester_det_eq_of_diagonal_charpoly
end SpectralRadiusUpperTail
