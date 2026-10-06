import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- Entrywise commutator of a matrix with one elementary skew direction.
The result is the common calculation behind scalar, pair and mixed real
Schur orbit coordinates. -/
theorem matrix_skew_single_commutator_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℝ) (u v r c : ι) :
    let K : Matrix ι ι ℝ :=
      Matrix.single u v (-1) + Matrix.single v u 1
    (K*T-T*K) r c =
      (if r=u then -T v c else 0) +
      (if r=v then T u c else 0) -
      (if c=v then -T r u else 0) -
      (if c=u then T r v else 0) := by
  have hL1 : (Matrix.single u v (-1 : ℝ)*T) r c =
      if r=u then -T v c else 0 := by
    by_cases h : r=u
    · subst r
      simp
    · rw [Matrix.single_mul_apply_of_ne (h := h)]
      simp [h]
  have hL2 : (Matrix.single v u (1 : ℝ)*T) r c =
      if r=v then T u c else 0 := by
    by_cases h : r=v
    · subst r
      simp
    · rw [Matrix.single_mul_apply_of_ne (h := h)]
      simp [h]
  have hR1 : (T*Matrix.single u v (-1 : ℝ)) r c =
      if c=v then -T r u else 0 := by
    by_cases h : c=v
    · subst c
      simp
    · rw [Matrix.mul_single_apply_of_ne (hbj := h)]
      simp [h]
  have hR2 : (T*Matrix.single v u (1 : ℝ)) r c =
      if c=u then T r v else 0 := by
    by_cases h : c=u
    · subst c
      simp
    · rw [Matrix.mul_single_apply_of_ne (hbj := h)]
      simp [h]
  dsimp
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_apply,
    Matrix.add_apply, hL1, hL2, hR1, hR2]
  abel

#print axioms matrix_skew_single_commutator_apply
end SpectralRadiusUpperTail
