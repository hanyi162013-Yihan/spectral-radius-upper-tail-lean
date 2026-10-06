import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- The two scalar shifts of a complex matrix multiply to a quadratic
matrix expression. This algebraic identity is the determinant bridge for
the nonreal marked-plane calculation. -/
theorem complex_matrix_conjugate_shift_factorization
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (x y : ℂ) :
    (((x+y) • (1 : Matrix ι ι ℂ)) - A) *
      (((x-y) • (1 : Matrix ι ι ℂ)) - A) =
      (x • (1 : Matrix ι ι ℂ) - A)^2 - y^2 • 1 := by
  let B : Matrix ι ι ℂ := x • 1 - A
  let C : Matrix ι ι ℂ := y • 1
  have hp : (x+y) • (1 : Matrix ι ι ℂ) - A = B+C := by
    dsimp [B, C]
    rw [add_smul]
    abel
  have hm : (x-y) • (1 : Matrix ι ι ℂ) - A = B-C := by
    dsimp [B, C]
    rw [sub_smul]
    abel
  have hc : B*C = C*B := by
    dsimp [C]
    rw [mul_smul_one, smul_one_mul]
  have hs : C^2 = y^2 • (1 : Matrix ι ι ℂ) := by
    dsimp [C]
    rw [pow_two, smul_one_mul, smul_smul, pow_two]
  rw [hp, hm]
  calc
    (B+C)*(B-C) = B*B-B*C+C*B-C*C := by noncomm_ring
    _ = B^2-C^2 := by rw [hc]; noncomm_ring
    _ = _ := by rw [hs]

#print axioms complex_matrix_conjugate_shift_factorization
end SpectralRadiusUpperTail
