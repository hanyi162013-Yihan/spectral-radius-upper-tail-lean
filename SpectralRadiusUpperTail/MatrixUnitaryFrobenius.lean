import SpectralRadiusUpperTail.FrobeniusTraceIdentity
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Frobenius

/-- The squared Frobenius norm of every matrix power is unchanged by
unitary similarity. This is the deterministic moment invariant used in a
Schur-coordinate representation. -/
theorem matrix_unitary_conjugation_frobenius_sq
    {𝕂 : Type*} [RCLike 𝕂] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) 𝕂)
    (U : Matrix.unitaryGroup (Fin n) 𝕂) :
    ‖(U : Matrix (Fin n) (Fin n) 𝕂) * A *
      (U : Matrix (Fin n) (Fin n) 𝕂)ᴴ‖^2 = ‖A‖^2 := by
  let u : Matrix (Fin n) (Fin n) 𝕂 := U
  have hu : uᴴ * u = 1 := by
    simpa [u, Matrix.star_eq_conjTranspose] using
      (Unitary.coe_star_mul_self U)
  rw [frobenius_norm_sq_trace, frobenius_norm_sq_trace]
  congr 1
  have hprod :
      (u * A * uᴴ) * (u * A * uᴴ)ᴴ = u * (A*Aᴴ) * uᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc uᴴ u, hu]
    simp only [Matrix.one_mul]
  rw [hprod, Matrix.trace_mul_cycle]
  simp only [hu, Matrix.one_mul]

theorem matrix_unitary_conjugation_power_frobenius_sq
    {𝕂 : Type*} [RCLike 𝕂] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) 𝕂)
    (U : Matrix.unitaryGroup (Fin n) 𝕂) (k : ℕ) :
    ‖((U : Matrix (Fin n) (Fin n) 𝕂) * A *
      (U : Matrix (Fin n) (Fin n) 𝕂)ᴴ)^k‖^2 = ‖A^k‖^2 := by
  let u : Matrix (Fin n) (Fin n) 𝕂 := U
  have hu : uᴴ * u = 1 := by
    simpa [u, Matrix.star_eq_conjTranspose] using
      (Unitary.coe_star_mul_self U)
  have hu' : u * uᴴ = 1 := by
    simpa [u, Matrix.star_eq_conjTranspose] using
      (Unitary.coe_mul_star_self U)
  have hpow (m : ℕ) : (u*A*uᴴ)^m = u*A^m*uᴴ := by
    induction m with
    | zero => simp [hu']
    | succ m ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc uᴴ u, hu]
      simp only [Matrix.one_mul]
  rw [hpow]
  exact matrix_unitary_conjugation_frobenius_sq (A^k) U

#print axioms matrix_unitary_conjugation_frobenius_sq
#print axioms matrix_unitary_conjugation_power_frobenius_sq
end SpectralRadiusUpperTail
