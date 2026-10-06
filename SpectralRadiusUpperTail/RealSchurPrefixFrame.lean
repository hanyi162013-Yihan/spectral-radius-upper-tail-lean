import SpectralRadiusUpperTail.RealSchurBlockFlagInvariant
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- The subspace spanned by all frame columns through block `k`. -/
noncomputable def realSchurPrefixSpan
    {ι β : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder β]
    (b : ι → β) (Q : Matrix ι ι ℝ) (k : β) :
    Submodule ℝ (ι → ℝ) :=
  Submodule.span ℝ (Q.col '' {j | b j ≤ k})

/-- The initial column span of an orthogonal block-upper
representation is invariant under the represented matrix. -/
theorem realSchurPrefixSpan_invariant
    {ι β : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder β]
    (b : ι → β) (A Q T : Matrix ι ι ℝ)
    (hQ : Qᵀ*Q=1) (hT : T.BlockTriangular b)
    (hA : A=Q*T*Qᵀ) (k : β) :
    ∀ v ∈ realSchurPrefixSpan b Q k, A.mulVecLin v ∈
      realSchurPrefixSpan b Q k := by
  rw [hA]
  exact orthogonal_blockUpper_prefixSpan_invariant b Q T hQ hT k

#print axioms realSchurPrefixSpan_invariant
end SpectralRadiusUpperTail
