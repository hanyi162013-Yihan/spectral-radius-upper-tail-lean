import SpectralRadiusUpperTail.RealSchurAllPairOrbitMatrix
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- The four coordinates of one lower 2×2 block form exactly one fiber of
the distance-lexicographic key. -/
def realSchurAllPairBlockEquiv {m : ℕ} (p : RealSchurLowerIndex m) :
    {z : RealSchurLowerIndex m × Fin 4 |
      realSchurLowerKey z.1 = realSchurLowerKey p} ≃ Fin 4 where
  toFun z := z.1.2
  invFun a := ⟨(p,a), rfl⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact realSchurLowerKey_injective z.2.symm
    · rfl
  right_inv _ := rfl

theorem realSchurAllPairOrbitMatrix_block_det {m : ℕ}
    (T : Matrix (Fin m) (Fin m) (Matrix (Fin 2) (Fin 2) ℝ))
    (x b c : Fin m → ℝ)
    (hdiag : ∀ i, T i i = realSchurBlock (x i) (b i) (c i))
    (p : RealSchurLowerIndex m) :
    ((realSchurAllPairOrbitMatrix T).toSquareBlock
      (fun z => realSchurLowerKey z.1) (realSchurLowerKey p)).det =
    (realSchurPairPairSylvester
      (x p.1.1) (b p.1.1) (c p.1.1)
      (x p.1.2) (b p.1.2) (c p.1.2)).det := by
  classical
  let e := realSchurAllPairBlockEquiv p
  let B := (realSchurAllPairOrbitMatrix T).toSquareBlock
    (fun z => realSchurLowerKey z.1) (realSchurLowerKey p)
  have hB : Matrix.reindex e e B =
      realSchurPairPairSylvester
        (x p.1.1) (b p.1.1) (c p.1.1)
        (x p.1.2) (b p.1.2) (c p.1.2) := by
    ext a s
    change realSchurAllPairOrbitMatrix T (p,a) (p,s) = _
    exact realSchurAllPairOrbitMatrix_diagonal T p
      (x p.1.1) (b p.1.1) (c p.1.1)
      (x p.1.2) (b p.1.2) (c p.1.2)
      (hdiag p.1.1) (hdiag p.1.2) a s
  calc
    B.det = (Matrix.reindex e e B).det :=
      (Matrix.det_reindex_self e B).symm
    _ = _ := congrArg Matrix.det hB

/-- The all-pair angular determinant is the product of the already
calculated pair–pair Sylvester determinants. This is the full finite block
Jacobian algebra for the all-pair chart, before global Schur coverage and
measure change are addressed. -/
theorem realSchurAllPairOrbitMatrix_det {m : ℕ}
    (T : Matrix (Fin m) (Fin m) (Matrix (Fin 2) (Fin 2) ℝ))
    (hT : ∀ a b : Fin m, b < a → T a b = 0)
    (x b c : Fin m → ℝ)
    (hdiag : ∀ i, T i i = realSchurBlock (x i) (b i) (c i)) :
    (realSchurAllPairOrbitMatrix T).det =
      ∏ p : RealSchurLowerIndex m,
        (realSchurPairPairSylvester
          (x p.1.1) (b p.1.1) (c p.1.1)
          (x p.1.2) (b p.1.2) (c p.1.2)).det := by
  classical
  let key := fun z : RealSchurLowerIndex m × Fin 4 => realSchurLowerKey z.1
  have htri : (realSchurAllPairOrbitMatrix T).BlockTriangular key :=
    realSchurAllPairOrbitMatrix_blockTriangular T hT
  have himage :
      (Finset.univ : Finset (RealSchurLowerIndex m × Fin 4)).image key =
        (Finset.univ : Finset (RealSchurLowerIndex m)).image realSchurLowerKey := by
    ext k
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z.1, rfl⟩
    · rintro ⟨p, rfl⟩
      exact ⟨(p,0), rfl⟩
  calc
    (realSchurAllPairOrbitMatrix T).det =
        ∏ a ∈ (Finset.univ : Finset (RealSchurLowerIndex m × Fin 4)).image key,
          ((realSchurAllPairOrbitMatrix T).toSquareBlock key a).det :=
      htri.det
    _ = ∏ a ∈ (Finset.univ : Finset (RealSchurLowerIndex m)).image realSchurLowerKey,
          ((realSchurAllPairOrbitMatrix T).toSquareBlock key a).det := by
      rw [himage]
    _ = ∏ p : RealSchurLowerIndex m,
          ((realSchurAllPairOrbitMatrix T).toSquareBlock key
            (realSchurLowerKey p)).det := by
      rw [Finset.prod_image (fun _ _ _ _ h => realSchurLowerKey_injective h)]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p _
      exact realSchurAllPairOrbitMatrix_block_det T x b c hdiag p

#print axioms realSchurAllPairOrbitMatrix_block_det
#print axioms realSchurAllPairOrbitMatrix_det
end SpectralRadiusUpperTail
