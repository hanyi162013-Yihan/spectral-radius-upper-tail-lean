import SpectralRadiusUpperTail.RealSchurMixedChartCharpoly
import SpectralRadiusUpperTail.RealSchurDiagonalCharpoly
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- The explicit real polynomial carried by a scalar or admissible
conjugate-pair Schur block. -/
noncomputable def RealSchurChartBlock.polynomial : RealSchurChartBlock → Polynomial ℝ
  | .scalar a => Polynomial.X - Polynomial.C a
  | .pair x _ _ y _ _ =>
      Polynomial.X^2 - Polynomial.C (2*x)*Polynomial.X +
        Polynomial.C (x^2+y^2)

theorem RealSchurChartBlock.charpoly_eq_polynomial
    (B : RealSchurChartBlock) :
    B.matrix.charpoly = B.polynomial := by
  cases B with
  | scalar a =>
    change (Matrix.scalar (Fin 1) a).charpoly =
      Polynomial.X - Polynomial.C a
    rw [Matrix.charpoly, Matrix.det_fin_one]
    simp [Matrix.charmatrix_apply, Matrix.scalar_apply]
  | pair x b c y hbc hy =>
    change (realSchurBlock x b c).charpoly =
      Polynomial.X^2 - Polynomial.C (2*x)*Polynomial.X +
        Polynomial.C (x^2+y^2)
    rw [realSchurBlock_charpoly, hbc]

theorem realSchurMixedChart_charpoly_explicit
    {m : ℕ} (B : Fin m → RealSchurChartBlock)
    (T : Matrix (RealSchurMixedCoord (fun i => (B i).size))
      (RealSchurMixedCoord (fun i => (B i).size)) ℝ)
    (hT : ∀ a b : Fin m, b < a →
      ∀ x : Fin ((B a).size), ∀ y : Fin ((B b).size),
        T ⟨a,x⟩ ⟨b,y⟩ = 0)
    (hdiag : ∀ i a b, T ⟨i,a⟩ ⟨i,b⟩ = (B i).matrix a b) :
    T.charpoly = ∏ i : Fin m, (B i).polynomial := by
  rw [realSchurMixedChart_charpoly_product B T hT hdiag]
  simp_rw [RealSchurChartBlock.charpoly_eq_polynomial]

#print axioms realSchurMixedChart_charpoly_explicit
end SpectralRadiusUpperTail
