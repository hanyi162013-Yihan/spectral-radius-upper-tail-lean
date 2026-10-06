import SpectralRadiusUpperTail.SchurBlockFlatten
import Mathlib.LinearAlgebra.Matrix.Trace

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Frobenius BigOperators

theorem real_frobenius_norm_sq_trace_finite {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) : ‖A‖^2=(A*Aᵀ).trace := by
  rw [real_frobenius_norm_sq_finite]
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.transpose_apply,pow_two]

/-- Adding zero coordinates through an isometric embedding preserves the
Frobenius norm, including for rectangular embeddings. -/
theorem rectangular_isometry_conjugation_norm_sq
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (P : Matrix κ ι ℝ) (hP : Pᵀ*P=1) (A : Matrix ι ι ℝ) :
    ‖P*A*Pᵀ‖^2=‖A‖^2 := by
  rw [real_frobenius_norm_sq_trace_finite,real_frobenius_norm_sq_trace_finite]
  simp only [Matrix.transpose_mul,Matrix.transpose_transpose]
  calc
    _ = (P*(A*(Pᵀ*P)*Aᵀ)*Pᵀ).trace := by simp only [Matrix.mul_assoc]
    _ = (P*(A*Aᵀ)*Pᵀ).trace := by rw [hP,Matrix.mul_one]
    _ = (Pᵀ*(P*(A*Aᵀ))).trace := Matrix.trace_mul_comm _ _
    _ = (A*Aᵀ).trace := by rw [← Matrix.mul_assoc,hP,Matrix.one_mul]

/-- Positive powers commute with padding by zero coordinates. The zero
power is excluded because the enlarged identity has additional entries. -/
theorem rectangular_isometry_conjugation_pow
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : Matrix κ ι ℝ) (hP : Pᵀ*P=1) (A : Matrix ι ι ℝ)
    (k : ℕ) (hk : 0 < k) : (P*A*Pᵀ)^k=P*A^k*Pᵀ := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  clear hk
  induction j with
  | zero => simp only [pow_one]
  | succ j ih =>
    calc
      _ = (P*A^(j+1)*Pᵀ)*(P*A*Pᵀ) := by rw [pow_succ,ih]
      _ = P*(A^(j+1)*(Pᵀ*P)*A)*Pᵀ := by simp only [Matrix.mul_assoc]
      _ = P*(A^(j+1)*A)*Pᵀ := by rw [hP,Matrix.mul_one]
      _ = _ := by rw [← pow_succ]

theorem rectangular_isometry_conjugation_power_norm_sq
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : Matrix κ ι ℝ) (hP : Pᵀ*P=1) (A : Matrix ι ι ℝ)
    (k : ℕ) (hk : 0 < k) : ‖(P*A*Pᵀ)^k‖^2=‖A^k‖^2 := by
  rw [rectangular_isometry_conjugation_pow P hP A k hk]
  exact rectangular_isometry_conjugation_norm_sq P hP (A^k)

#print axioms rectangular_isometry_conjugation_norm_sq
#print axioms rectangular_isometry_conjugation_pow
#print axioms rectangular_isometry_conjugation_power_norm_sq
end SpectralRadiusUpperTail
