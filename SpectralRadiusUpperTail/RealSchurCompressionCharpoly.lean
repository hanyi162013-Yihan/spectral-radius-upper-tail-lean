import SpectralRadiusUpperTail.RealSchurTwoBlockCharpoly
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- Replacing a subtype predicate by an equivalent predicate does not
change the characteristic polynomial of the compressed matrix. -/
theorem matrix_compression_charpoly_congr
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℝ) (p q : ι → Prop)
    [DecidablePred p] [DecidablePred q]
    (hpq : ∀ i, p i ↔ q i) :
    (T.toSquareBlockProp p).charpoly =
      (T.toSquareBlockProp q).charpoly := by
  let e : {i : ι // p i} ≃ {i : ι // q i} :=
    Equiv.subtypeEquivRight hpq
  have hmatrix : Matrix.reindex e e (T.toSquareBlockProp p) =
      T.toSquareBlockProp q := by
    ext i j
    rfl
  rw [← hmatrix, Matrix.charpoly_reindex]

/-- At any block cut, the characteristic polynomial factors into the
leading and trailing compressed characteristic polynomials. -/
theorem blockUpper_charpoly_prefix_suffix
    {ι β : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder β]
    (b : ι → β) (T : Matrix ι ι ℝ)
    (hT : T.BlockTriangular b) (k : β) :
    T.charpoly =
      (T.submatrix (Subtype.val : {i : ι // b i ≤ k} → ι)
        (Subtype.val : {i : ι // b i ≤ k} → ι)).charpoly *
      (T.submatrix (Subtype.val : {i : ι // k < b i} → ι)
        (Subtype.val : {i : ι // k < b i} → ι)).charpoly := by
  classical
  have hzero : ∀ i, ¬b i ≤ k → ∀ j, b j ≤ k → T i j = 0 := by
    intro i hi j hj
    exact hT (lt_of_le_of_lt hj (lt_of_not_ge hi))
  have hfactor := matrix_twoBlockUpper_charpoly T
    (fun i => b i ≤ k) hzero
  have hcongr := matrix_compression_charpoly_congr T
    (fun i => ¬b i ≤ k) (fun i => k < b i)
    (fun i => ⟨lt_of_not_ge, not_le_of_gt⟩)
  calc
    T.charpoly = (T.toSquareBlockProp (fun i => b i ≤ k)).charpoly *
        (T.toSquareBlockProp (fun i => ¬b i ≤ k)).charpoly := hfactor
    _ = (T.toSquareBlockProp (fun i => b i ≤ k)).charpoly *
        (T.toSquareBlockProp (fun i => k < b i)).charpoly := by rw [hcongr]
    _ = _ := rfl

#print axioms matrix_compression_charpoly_congr
#print axioms blockUpper_charpoly_prefix_suffix
end SpectralRadiusUpperTail
