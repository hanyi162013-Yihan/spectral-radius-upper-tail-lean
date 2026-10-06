import SpectralRadiusUpperTail.RealSchurInvariantSubspaceSeed
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- If the first family of orthogonal columns spans an invariant
subspace, the conjugated matrix has a zero lower-left block. This is
the matrix algebra required after extending an invariant line or
plane to an orthonormal basis. -/
theorem realMatrix_orthogonal_invariant_columns_lower_zero
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (A Q : Matrix ι ι ℝ) (hQ : Qᵀ*Q=1)
    (S : Set ι)
    (hInv : ∀ j ∈ S,
      A.mulVec (Q.col j) ∈ Submodule.span ℝ (Q.col '' S))
    (i j : ι) (hi : i ∉ S) (hj : j ∈ S) :
    (Qᵀ*A*Q) i j = 0 := by
  let P : Submodule ℝ (ι → ℝ) := Submodule.span ℝ (Q.col '' S)
  have hkill : ∀ v ∈ P, ((Qᵀ).mulVec v) i = 0 := by
    intro v hv
    refine Submodule.span_induction (fun w hw => ?_) ?_
      (fun x y _ _ hx hy => ?_) (fun a x _ hx => ?_) hv
    · obtain ⟨k,hk,rfl⟩ := hw
      have hik : i ≠ k := by
        intro heq
        subst k
        exact hi hk
      calc
        ((Qᵀ).mulVec (Q.col k)) i = (Qᵀ*Q) i k := rfl
        _ = 0 := by rw [hQ]; simp [hik]
    · simp
    · rw [Matrix.mulVec_add, Pi.add_apply, hx, hy, add_zero]
    · rw [Matrix.mulVec_smul, Pi.smul_apply, hx, smul_zero]
  have hAj : A.mulVec (Q.col j) ∈ P := hInv j hj
  have hz := hkill (A.mulVec (Q.col j)) hAj
  rw [Matrix.mul_assoc]
  change ((Qᵀ).mulVec ((A*Q).col j)) i = 0
  change ((Qᵀ).mulVec (A.mulVec (Q.col j))) i = 0
  exact hz

#print axioms realMatrix_orthogonal_invariant_columns_lower_zero
end SpectralRadiusUpperTail
