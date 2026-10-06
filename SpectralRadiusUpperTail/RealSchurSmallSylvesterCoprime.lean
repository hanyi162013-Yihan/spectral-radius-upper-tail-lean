import SpectralRadiusUpperTail.RealSchurScalarPairCoprime
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- Every 1×1 real matrix is its unique diagonal entry times the identity. -/
theorem realSchur_fin_one_eq_scalar (A : Matrix (Fin 1) (Fin 1) ℝ) :
    A = Matrix.scalar (Fin 1) (A 0 0) := by
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.scalar]

/-- For block sizes one or two, coprime characteristic polynomials
make the rectangular Sylvester bridge nonsingular. -/
theorem realSchurRectangularSylvester_ne_zero_of_coprime_small
    {a b : ℕ} (ha : a = 1 ∨ a = 2) (hb : b = 1 ∨ b = 2)
    (A : Matrix (Fin a) (Fin a) ℝ)
    (B : Matrix (Fin b) (Fin b) ℝ)
    (hcop : IsCoprime A.charpoly B.charpoly) :
    (realSchurRectangularSylvester A B).det ≠ 0 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rw [realSchur_fin_one_eq_scalar A,
      realSchur_fin_one_eq_scalar B] at hcop ⊢
    exact realSchurRectangularSylvester_scalar_scalar_ne_zero_of_coprime
      (A 0 0) (B 0 0) hcop
  · rw [realSchur_fin_one_eq_scalar A] at hcop ⊢
    exact realSchurRectangularSylvester_scalar_pair_ne_zero_of_coprime
      (A 0 0) B hcop
  · rw [realSchur_fin_one_eq_scalar B] at hcop ⊢
    exact realSchurRectangularSylvester_pair_scalar_ne_zero_of_coprime
      A (B 0 0) hcop
  · exact realSchurRectangularSylvester_pair_pair_ne_zero_of_coprime A B hcop

#print axioms realSchurRectangularSylvester_ne_zero_of_coprime_small
end SpectralRadiusUpperTail
