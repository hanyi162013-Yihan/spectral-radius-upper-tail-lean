import SpectralRadiusUpperTail.RealSchurBlockOrthogonalRigidity
import SpectralRadiusUpperTail.RealSchurOrthogonalInvariantBlock
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- Equality of one initial column span forces the corresponding
off-flag entries of the relative orthogonal frame to vanish. -/
theorem orthogonal_equalColumnSpan_transition_zero
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (Q R : Matrix ι ι ℝ) (hQ : Qᵀ*Q=1)
    (S : Set ι)
    (hspan : Submodule.span ℝ (Q.col '' S) =
      Submodule.span ℝ (R.col '' S))
    (i j : ι) (hi : i ∉ S) (hj : j ∈ S) :
    (Qᵀ*R) i j = 0 := by
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
  have hRj : R.col j ∈ P := by
    change R.col j ∈ Submodule.span ℝ (Q.col '' S)
    rw [hspan]
    exact Submodule.subset_span ⟨j,hj,rfl⟩
  change ((Qᵀ).mulVec (R.col j)) i = 0
  exact hkill (R.col j) hRj

/-- Equal column spans at every block prefix make the relative frame
block upper triangular. -/
theorem orthogonal_equalBlockFlags_transition_upper
    {ι β : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder β]
    (b : ι → β) (Q R : Matrix ι ι ℝ) (hQ : Qᵀ*Q=1)
    (hflags : ∀ k : β,
      Submodule.span ℝ (Q.col '' {j | b j ≤ k}) =
        Submodule.span ℝ (R.col '' {j | b j ≤ k})) :
    (Qᵀ*R).BlockTriangular b := by
  intro i j hij
  exact orthogonal_equalColumnSpan_transition_zero ι Q R hQ
    {z | b z ≤ b j} (hflags (b j)) i j (not_le.mpr hij) le_rfl

/-- For two orthogonal frames with the same ordered block flag, the
transition acts within blocks only. -/
theorem orthogonal_equalBlockFlags_transition_offBlock
    {ι β : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder β]
    (b : ι → β) (Q R : Matrix ι ι ℝ)
    (hQ : Qᵀ*Q=1) (hR : Rᵀ*R=1)
    (hflags : ∀ k : β,
      Submodule.span ℝ (Q.col '' {j | b j ≤ k}) =
        Submodule.span ℝ (R.col '' {j | b j ≤ k}))
    (i j : ι) (hij : b i ≠ b j) :
    (Qᵀ*R) i j = 0 := by
  have hQR : (Qᵀ*R)ᵀ*(Qᵀ*R)=1 := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc
      (Rᵀ*Q)*(Qᵀ*R) = Rᵀ*(Q*Qᵀ)*R := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [mul_eq_one_comm.mp hQ, Matrix.mul_one, hR]
  exact orthogonal_blockTriangular_offBlock b (Qᵀ*R) hQR
    (orthogonal_equalBlockFlags_transition_upper b Q R hQ hflags) i j hij

#print axioms orthogonal_equalBlockFlags_transition_offBlock
end SpectralRadiusUpperTail
