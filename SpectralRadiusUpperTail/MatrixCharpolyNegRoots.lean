import SpectralRadiusUpperTail.MatrixExteriorRootPowerPartition
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- Negating a finite complex matrix negates its characteristic roots,
including algebraic multiplicities. -/
theorem matrix_charpoly_neg_roots {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    (-A).charpoly.roots = A.charpoly.roots.map Neg.neg := by
  classical
  have hchar : (-A).charpoly =
      ((-1 : ℂ)^n) • (A.charpoly.comp (-Polynomial.X)) := by
    apply Polynomial.funext
    intro z
    rw [Matrix.eval_charpoly, Polynomial.eval_smul,
      Polynomial.eval_comp, Polynomial.eval_neg,
      Polynomial.eval_X, Matrix.eval_charpoly]
    have hmat : Matrix.scalar (Fin n) z - (-A) =
        -(Matrix.scalar (Fin n) (-z) - A) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [Matrix.scalar_apply]
        ring
      · simp [Matrix.scalar_apply, hij]
    rw [hmat, Matrix.det_neg]
    simp only [Fintype.card_fin]
    ring
  rw [hchar, Polynomial.roots_smul_nonzero]
  · exact Polynomial.roots_comp_neg_X _
  · exact pow_ne_zero _ (by norm_num)

/-- Sign reversal interchanges the two weighted real half-lines. -/
theorem matrixPositiveRealExteriorPower_neg {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    matrixPositiveRealExteriorPower (-A) k =
      matrixNegativeRealExteriorPower A k := by
  classical
  unfold matrixPositiveRealExteriorPower matrixNegativeRealExteriorPower
  rw [matrix_charpoly_neg_roots]
  simp only [Multiset.map_map]
  have hfun :
      (fun z : ℂ => if z.im = 0 ∧ 1 < z.re then z.re^(2*k) else 0) ∘ Neg.neg =
      (fun z : ℂ => if z.im = 0 ∧ z.re < -1 then (-z.re)^(2*k) else 0) := by
    funext z
    have hlt : (1 : ℝ) < -z.re ↔ z.re < -1 := by
      constructor <;> intro h <;> linarith
    simp only [Function.comp_apply, Complex.neg_im, Complex.neg_re,
      neg_eq_zero, hlt]
  rw [hfun]

#print axioms matrix_charpoly_neg_roots
#print axioms matrixPositiveRealExteriorPower_neg
end SpectralRadiusUpperTail
