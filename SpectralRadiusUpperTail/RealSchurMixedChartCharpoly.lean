import SpectralRadiusUpperTail.RealSchurMixedBlockCharpoly
import SpectralRadiusUpperTail.RealSchurMixedBlockGap
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

/-- The subtype indexing a chosen diagonal block is canonically the
finite coordinate type of that block. -/
def realSchurMixedBlockFiberEquiv
    {m : ℕ} (s : Fin m → ℕ) (i : Fin m) :
    Fin (s i) ≃
      {z : RealSchurMixedCoord s // z.1 = i} where
  toFun a := ⟨⟨i,a⟩,rfl⟩
  invFun z := Fin.cast (congrArg s z.property) z.val.2
  left_inv a := rfl
  right_inv z := by
    rcases z with ⟨⟨j,a⟩,h⟩
    cases h
    rfl

/-- The native diagonal block of the global matrix has the characteristic
polynomial of its named scalar or conjugate-pair block. -/
theorem realSchurMixedChart_diagonalBlock_charpoly
    {m : ℕ} (B : Fin m → RealSchurChartBlock)
    (T : Matrix (RealSchurMixedCoord (fun i => (B i).size))
      (RealSchurMixedCoord (fun i => (B i).size)) ℝ)
    (hdiag : ∀ i a b, T ⟨i,a⟩ ⟨i,b⟩ = (B i).matrix a b)
    (i : Fin m) :
    (T.toSquareBlock
      (fun z : RealSchurMixedCoord (fun i => (B i).size) => z.1) i).charpoly =
        (B i).matrix.charpoly := by
  let e := realSchurMixedBlockFiberEquiv (fun i => (B i).size) i
  have heq : Matrix.reindex e.symm e.symm
      (T.toSquareBlock
        (fun z : RealSchurMixedCoord (fun i => (B i).size) => z.1) i) =
        (B i).matrix := by
    ext a b
    exact hdiag i a b
  calc
    _ = (Matrix.reindex e.symm e.symm
        (T.toSquareBlock
          (fun z : RealSchurMixedCoord (fun i => (B i).size) => z.1) i)).charpoly :=
      (Matrix.charpoly_reindex e.symm _).symm
    _ = (B i).matrix.charpoly := by rw [heq]

/-- Every local real-Schur block-upper center has characteristic
polynomial equal to the product of the named 1×1/2×2 block polynomials. -/
theorem realSchurMixedChart_charpoly_product
    {m : ℕ} (B : Fin m → RealSchurChartBlock)
    (T : Matrix (RealSchurMixedCoord (fun i => (B i).size))
      (RealSchurMixedCoord (fun i => (B i).size)) ℝ)
    (hT : ∀ a b : Fin m, b < a →
      ∀ x : Fin ((B a).size), ∀ y : Fin ((B b).size),
        T ⟨a,x⟩ ⟨b,y⟩ = 0)
    (hdiag : ∀ i a b, T ⟨i,a⟩ ⟨i,b⟩ = (B i).matrix a b) :
    T.charpoly = ∏ i : Fin m, (B i).matrix.charpoly := by
  have hproj : realSchurMixedLowerProjection (fun i => (B i).size) T = 0 := by
    funext p
    exact hT p.1.1.1 p.1.1.2 p.1.2 p.2.1 p.2.2
  rw [realSchurMixed_blockUpper_charpoly (fun i => (B i).size)
    (fun i => (B i).size_pos) T hproj]
  simp_rw [realSchurMixedChart_diagonalBlock_charpoly B T hdiag]

#print axioms realSchurMixedChart_charpoly_product
end SpectralRadiusUpperTail
