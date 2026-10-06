import SpectralRadiusUpperTail.RealSchurColumnSpanSupport
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- A block-upper matrix preserves every initial block column span
after conjugation by an orthogonal frame. -/
theorem orthogonal_blockUpper_prefixSpan_invariant
    {ι β : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder β]
    (b : ι → β) (Q T : Matrix ι ι ℝ)
    (hQ : Qᵀ*Q=1) (hT : T.BlockTriangular b)
    (k : β) :
    ∀ v ∈ Submodule.span ℝ (Q.col '' {j | b j ≤ k}),
      (Q*T*Qᵀ).mulVec v ∈
        Submodule.span ℝ (Q.col '' {j | b j ≤ k}) := by
  let S : Set ι := {j | b j ≤ k}
  let P : Submodule ℝ (ι → ℝ) := Submodule.span ℝ (Q.col '' S)
  have hAQ : (Q*T*Qᵀ)*Q=Q*T := by
    calc
      (Q*T*Qᵀ)*Q = (Q*T)*(Qᵀ*Q) := by rw [Matrix.mul_assoc]
      _ = Q*T := by rw [hQ, Matrix.mul_one]
  intro v hv
  change (Q*T*Qᵀ).mulVec v ∈ P
  refine Submodule.span_induction (fun w hw => ?_) ?_
    (fun x y _ _ hx hy => ?_) (fun a x _ hx => ?_) hv
  · obtain ⟨j,hj,rfl⟩ := hw
    have hcol : ∀ i, i ∉ S → T.col j i = 0 := by
      intro i hi
      have hki : k < b i := lt_of_not_ge hi
      exact hT (lt_of_le_of_lt hj hki)
    have hmem := matrix_mulVec_mem_columnSpan_of_support ι Q S
      (T.col j) hcol
    change Q.mulVec (T.col j) ∈ P at hmem
    change ((Q*T*Qᵀ)*Q).col j ∈ P
    rw [hAQ]
    exact hmem
  · simp
  · rw [Matrix.mulVec_add]
    exact P.add_mem hx hy
  · rw [Matrix.mulVec_smul]
    exact P.smul_mem a hx

#print axioms orthogonal_blockUpper_prefixSpan_invariant
end SpectralRadiusUpperTail
