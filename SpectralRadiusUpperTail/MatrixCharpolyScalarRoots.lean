import SpectralRadiusUpperTail.MatrixCharpolyNegRoots
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- Multiplication of a complex matrix by a nonzero scalar multiplies every
characteristic root by that scalar, with algebraic multiplicities. -/
theorem matrix_charpoly_smul_roots {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (hc : c ≠ 0) :
    (c • A).charpoly.roots = A.charpoly.roots.map (fun z => c*z) := by
  classical
  have hchar : (c • A).charpoly =
      (c^n) • (A.charpoly.comp (Polynomial.C c⁻¹ * Polynomial.X)) := by
    apply Polynomial.funext
    intro z
    rw [Matrix.eval_charpoly, Polynomial.eval_smul,
      Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Matrix.eval_charpoly]
    have hmat : Matrix.scalar (Fin n) z - c • A =
        c • (Matrix.scalar (Fin n) (c⁻¹*z) - A) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [Matrix.scalar_apply, Matrix.sub_apply, Matrix.smul_apply,
          smul_eq_mul]
        field_simp [hc]
      · simp [Matrix.scalar_apply, Matrix.sub_apply, Matrix.smul_apply,
          smul_eq_mul, hij]
    rw [hmat, Matrix.det_smul]
    simp only [Fintype.card_fin]
    ring
  rw [hchar, Polynomial.roots_smul_nonzero]
  · simpa [Polynomial.roots_comp_C_mul_X_add_C, hc,
      inv_inv] using
      (Polynomial.roots_comp_C_mul_X_add_C A.charpoly c⁻¹ 0
        (isUnit_iff_ne_zero.mpr (inv_ne_zero hc)))
  · exact pow_ne_zero _ hc

#print axioms matrix_charpoly_smul_roots
end SpectralRadiusUpperTail
