import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- A two-block upper-triangular matrix has characteristic polynomial
the product of its leading and trailing diagonal compressions. -/
theorem matrix_twoBlockUpper_charpoly
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℝ) (p : ι → Prop) [DecidablePred p]
    (hT : ∀ i, ¬p i → ∀ j, p j → T i j = 0) :
    T.charpoly = (T.toSquareBlockProp p).charpoly *
      (T.toSquareBlockProp (fun i => ¬p i)).charpoly := by
  have hchar : ∀ i, ¬p i → ∀ j, p j → T.charmatrix i j = 0 := by
    intro i hi j hj
    have hij : i ≠ j := by
      intro e
      subst j
      exact hi hj
    rw [Matrix.charmatrix_apply_ne T i j hij, hT i hi j hj]
    simp
  have hprefix : (T.charmatrix).toSquareBlockProp p =
      (T.toSquareBlockProp p).charmatrix := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.toSquareBlockProp_def]
    · have hval : (i : ι) ≠ (j : ι) := by
        intro e
        exact hij (Subtype.ext e)
      simp [Matrix.toSquareBlockProp_def,
        Matrix.charmatrix_apply_ne, hij, hval]
  have hsuffix : (T.charmatrix).toSquareBlockProp (fun i => ¬p i) =
      (T.toSquareBlockProp (fun i => ¬p i)).charmatrix := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.toSquareBlockProp_def]
    · have hval : (i : ι) ≠ (j : ι) := by
        intro e
        exact hij (Subtype.ext e)
      simp [Matrix.toSquareBlockProp_def,
        Matrix.charmatrix_apply_ne, hij, hval]
  calc
    T.charpoly = T.charmatrix.det := rfl
    _ = ((T.charmatrix).toSquareBlockProp p).det *
        ((T.charmatrix).toSquareBlockProp (fun i => ¬p i)).det :=
      Matrix.twoBlockTriangular_det T.charmatrix p hchar
    _ = (T.toSquareBlockProp p).charpoly *
        (T.toSquareBlockProp (fun i => ¬p i)).charpoly := by
      rw [hprefix, hsuffix]
      rfl

#print axioms matrix_twoBlockUpper_charpoly
end SpectralRadiusUpperTail
