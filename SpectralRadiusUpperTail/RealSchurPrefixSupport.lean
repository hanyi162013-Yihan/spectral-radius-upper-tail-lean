import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- A block-upper matrix preserves vectors supported on the first
blocks. This gives the concrete coordinate model of a Schur flag. -/
theorem blockUpper_mulVec_prefix_support
    {ι β : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder β]
    (b : ι → β) (T : Matrix ι ι ℝ) (hT : T.BlockTriangular b)
    (k : β) (v : ι → ℝ)
    (hv : ∀ j, k < b j → v j = 0)
    (i : ι) (hi : k < b i) :
    T.mulVec v i = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hkj : b j ≤ k
  · rw [hT (lt_of_le_of_lt hkj hi), zero_mul]
  · rw [hv j (lt_of_not_ge hkj), mul_zero]

#print axioms blockUpper_mulVec_prefix_support
end SpectralRadiusUpperTail
