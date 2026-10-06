import SpectralRadiusUpperTail.SigmaBlockFiberEquiv
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- A block-triangular matrix on a dependent sum has determinant equal to
the product of its variable-sized diagonal block determinants. The block
key may live in a larger ordered type, provided it is injective. -/
theorem determinant_of_sigma_block_triangular
    {I A : Type*} [Fintype I] [DecidableEq I]
    [LinearOrder A] [DecidableEq A]
    (F : I → Type*) [∀ i, Fintype (F i)] [∀ i, DecidableEq (F i)]
    (hF : ∀ i, Nonempty (F i))
    (b : I → A) (hb : Function.Injective b)
    (M : Matrix (Σ i, F i) (Σ i, F i) ℝ)
    (htri : M.BlockTriangular (fun z => b z.1)) :
    M.det = ∏ i : I,
      (Matrix.of (fun x y : F i => M ⟨i,x⟩ ⟨i,y⟩)).det := by
  classical
  have hblock (i : I) :
      (M.toSquareBlock (fun z => b z.1) (b i)).det =
        (Matrix.of (fun x y : F i => M ⟨i,x⟩ ⟨i,y⟩)).det := by
    let e := sigmaBlockFiberEquiv F b hb i
    let B := M.toSquareBlock (fun z => b z.1) (b i)
    have hB : Matrix.reindex e e B =
        Matrix.of (fun x y : F i => M ⟨i,x⟩ ⟨i,y⟩) := by
      ext x y
      rfl
    calc
      B.det = (Matrix.reindex e e B).det :=
        (Matrix.det_reindex_self e B).symm
      _ = _ := congrArg Matrix.det hB
  have himage :
      (Finset.univ : Finset (Σ i, F i)).image (fun z => b z.1) =
        (Finset.univ : Finset I).image b := by
    ext a
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨i,x⟩,h⟩
      exact ⟨i,h⟩
    · rintro ⟨i,h⟩
      exact ⟨⟨i,Classical.choice (hF i)⟩,h⟩
  calc
    M.det = ∏ a ∈ (Finset.univ : Finset (Σ i, F i)).image (fun z => b z.1),
        (M.toSquareBlock (fun z => b z.1) a).det := htri.det
    _ = ∏ a ∈ (Finset.univ : Finset I).image b,
        (M.toSquareBlock (fun z => b z.1) a).det := by rw [himage]
    _ = ∏ i : I, (M.toSquareBlock (fun z => b z.1) (b i)).det := by
      rw [Finset.prod_image (fun _ _ _ _ h => hb h)]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      exact hblock i

#print axioms determinant_of_sigma_block_triangular
end SpectralRadiusUpperTail
