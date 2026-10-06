import SpectralRadiusUpperTail.RealSchurOrthogonalFlagTransition
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- A coordinate vector supported in `S` is sent by a matrix into the
span of the corresponding columns. -/
theorem matrix_mulVec_mem_columnSpan_of_support
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℝ) (S : Set ι)
    (v : ι → ℝ) (hv : ∀ j, j ∉ S → v j = 0) :
    Q.mulVec v ∈ Submodule.span ℝ (Q.col '' S) := by
  let P : Submodule ℝ (ι → ℝ) := Submodule.span ℝ (Q.col '' S)
  rw [Matrix.mulVec_eq_sum]
  apply Submodule.sum_mem P
  intro j hj
  have hcol : Qᵀ j = Q.col j := by
    funext i
    rfl
  by_cases hS : j ∈ S
  · simpa only [op_smul_eq_smul, hcol] using
      (P.smul_mem (v j) (Submodule.subset_span ⟨j,hS,rfl⟩))
  · simp [hv j hS]

#print axioms matrix_mulVec_mem_columnSpan_of_support
end SpectralRadiusUpperTail
