import SpectralRadiusUpperTail.SchurStrictTailFirstVertex
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- Regroup a strict tail by its first vertex. -/
theorem schurStrictTailFirstVertex_sum (N l : ℕ) (i : Fin N)
    {M : Type*} [AddCommMonoid M]
    (f : {q : IncreasingBlockPath N l // i < q.val 0} → M) :
    (∑ q, f q) =
      ∑ h : {h : Fin N // i < h},
        ∑ q : {q : IncreasingBlockPath N l // q.val 0 = h.val},
          f ⟨q.val, h.property.trans_eq q.property.symm⟩ := by
  let e := schurStrictTailFirstVertexEquiv N l i
  conv_lhs => rw [← e.symm.sum_comp]
  rw [Fintype.sum_sigma]
  rfl

#print axioms schurStrictTailFirstVertex_sum
end SpectralRadiusUpperTail
