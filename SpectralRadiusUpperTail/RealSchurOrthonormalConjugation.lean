import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- The change-of-basis matrix between real orthonormal bases is
orthogonal, and it conjugates the two matrices of an endomorphism. -/
theorem realOrthonormalBasis_matrix_conjugation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u b : OrthonormalBasis ι ℝ E) (f : E →ₗ[ℝ] E) :
    let Q := u.toBasis.toMatrix b
    Qᵀ * Q = 1 ∧
      LinearMap.toMatrix u.toBasis u.toBasis f =
        Q * (LinearMap.toMatrix b.toBasis b.toBasis f) * Qᵀ := by
  let Q := u.toBasis.toMatrix b
  let R := b.toBasis.toMatrix u
  have horth : Qᵀ * Q = 1 := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (OrthonormalBasis.toMatrix_orthonormalBasis_conjTranspose_mul_self u b)
  have hQR : Q * R = 1 :=
    u.toBasis.toMatrix_mul_toMatrix_flip b.toBasis
  have hR : Qᵀ = R := by
    calc
      Qᵀ = Qᵀ * 1 := by simp
      _ = Qᵀ * (Q * R) := by rw [hQR]
      _ = (Qᵀ * Q) * R := by rw [Matrix.mul_assoc]
      _ = R := by rw [horth]; simp
  have h1 : Q * (LinearMap.toMatrix b.toBasis b.toBasis f) =
      LinearMap.toMatrix b.toBasis u.toBasis f := by
    simpa [Q] using
      (LinearMap.toMatrix_comp b.toBasis b.toBasis u.toBasis
        (LinearMap.id : E →ₗ[ℝ] E) f).symm
  have h2 : (LinearMap.toMatrix b.toBasis u.toBasis f) * R =
      LinearMap.toMatrix u.toBasis u.toBasis f := by
    simpa [R] using
      (LinearMap.toMatrix_comp u.toBasis b.toBasis u.toBasis
        f (LinearMap.id : E →ₗ[ℝ] E)).symm
  refine ⟨horth, ?_⟩
  rw [← h2, ← hR, ← h1]

#print axioms realOrthonormalBasis_matrix_conjugation
end SpectralRadiusUpperTail
