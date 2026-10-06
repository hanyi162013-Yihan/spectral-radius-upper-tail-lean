import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

private theorem sum_eq_sum_subtype_of_zero
    {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    (f : ι → ℝ) (hz : ∀ i, ¬p i → f i = 0) :
    (∑ i, f i) = ∑ i : {i // p i}, f i := by
  calc
    (∑ i, f i) = ∑ i, if p i then f i else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hp : p i
      · simp [hp]
      · simp [hp, hz i hp]
    _ = ∑ i : {i // p i}, f i := by
      have hsum := Finset.sum_subtype_eq_sum_filter
        (s := Finset.univ) (f := f) (p := p)
      simpa only [Finset.sum_filter, Finset.subtype_univ] using hsum.symm

/-- The lower-left corner of an intertwiner between two block-upper
matrices itself intertwines the trailing and leading diagonal
compressions. -/
theorem blockUpper_intertwiner_lowerCorner
    {ι β : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder β]
    (b : ι → β) (T U X : Matrix ι ι ℝ)
    (hT : T.BlockTriangular b) (hU : U.BlockTriangular b)
    (hX : T*X=X*U) (k : β) :
    let P := {i : ι // b i ≤ k}
    let C := {i : ι // k < b i}
    (T.submatrix (Subtype.val : C → ι) (Subtype.val : C → ι)) *
      (X.submatrix (Subtype.val : C → ι) (Subtype.val : P → ι)) =
    (X.submatrix (Subtype.val : C → ι) (Subtype.val : P → ι)) *
      (U.submatrix (Subtype.val : P → ι) (Subtype.val : P → ι)) := by
  classical
  dsimp only
  ext i j
  have hleft : (∑ l : ι, T i l * X l j) =
      ∑ l : {z : ι // k < b z}, T i l * X l j := by
    apply sum_eq_sum_subtype_of_zero
    intro l hl
    have hkl : b l ≤ k := le_of_not_gt hl
    rw [hT (lt_of_le_of_lt hkl i.property), zero_mul]
  have hright : (∑ l : ι, X i l * U l j) =
      ∑ l : {z : ι // b z ≤ k}, X i l * U l j := by
    apply sum_eq_sum_subtype_of_zero
    intro l hl
    have hkl : k < b l := lt_of_not_ge hl
    rw [hU (lt_of_le_of_lt j.property hkl), mul_zero]
  have heq := congrArg (fun M : Matrix ι ι ℝ => M i j) hX
  simp only [Matrix.mul_apply] at heq ⊢
  exact hleft.symm.trans (heq.trans hright)

#print axioms blockUpper_intertwiner_lowerCorner
end SpectralRadiusUpperTail
