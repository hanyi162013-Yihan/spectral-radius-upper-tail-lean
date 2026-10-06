import SpectralRadiusUpperTail.RealSchurQuadraticCoprimeResultant
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Polynomial

theorem realSchurScalar_charpoly (a : ℝ) :
    (Matrix.scalar (Fin 1) a).charpoly = X - C a := by
  rw [Matrix.charpoly, Matrix.det_fin_one]
  simp [Matrix.scalar_apply]

theorem realSchur_scalar_pair_eval_ne_zero_of_coprime
    (a : ℝ) (B : Matrix (Fin 2) (Fin 2) ℝ)
    (hcop : IsCoprime (Matrix.scalar (Fin 1) a).charpoly B.charpoly) :
    a^2-a*B.trace+B.det ≠ 0 := by
  rcases aeval_ne_zero_of_isCoprime hcop a with h | h
  · rw [realSchurScalar_charpoly] at h
    simp at h
  · have hp : B.charpoly.eval a ≠ 0 := by simpa using h
    have heval : B.charpoly.eval a = a^2-a*B.trace+B.det := by
      rw [Matrix.charpoly_fin_two]
      simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
      ring
    rw [heval] at hp
    exact hp

theorem realSchurRectangularSylvester_scalar_scalar_ne_zero_of_coprime
    (a u : ℝ)
    (hcop : IsCoprime (Matrix.scalar (Fin 1) a).charpoly
      (Matrix.scalar (Fin 1) u).charpoly) :
    (realSchurRectangularSylvester
      (Matrix.scalar (Fin 1) a) (Matrix.scalar (Fin 1) u)).det ≠ 0 := by
  rw [realSchurRectangularSylvester_scalar_scalar]
  rcases aeval_ne_zero_of_isCoprime hcop a with h | h
  · rw [realSchurScalar_charpoly] at h
    simp at h
  · rw [realSchurScalar_charpoly] at h
    simpa using h

theorem realSchurRectangularSylvester_scalar_pair_ne_zero_of_coprime
    (a : ℝ) (B : Matrix (Fin 2) (Fin 2) ℝ)
    (hcop : IsCoprime (Matrix.scalar (Fin 1) a).charpoly B.charpoly) :
    (realSchurRectangularSylvester
      (Matrix.scalar (Fin 1) a) B).det ≠ 0 := by
  rw [realSchurRectangularSylvester_scalar_pair_general]
  exact realSchur_scalar_pair_eval_ne_zero_of_coprime a B hcop

theorem realSchurRectangularSylvester_pair_scalar_ne_zero_of_coprime
    (A : Matrix (Fin 2) (Fin 2) ℝ) (u : ℝ)
    (hcop : IsCoprime A.charpoly (Matrix.scalar (Fin 1) u).charpoly) :
    (realSchurRectangularSylvester
      A (Matrix.scalar (Fin 1) u)).det ≠ 0 := by
  rw [realSchurRectangularSylvester_pair_scalar_general]
  exact realSchur_scalar_pair_eval_ne_zero_of_coprime u A hcop.symm

#print axioms realSchurRectangularSylvester_scalar_scalar_ne_zero_of_coprime
#print axioms realSchurRectangularSylvester_scalar_pair_ne_zero_of_coprime
#print axioms realSchurRectangularSylvester_pair_scalar_ne_zero_of_coprime
end SpectralRadiusUpperTail
