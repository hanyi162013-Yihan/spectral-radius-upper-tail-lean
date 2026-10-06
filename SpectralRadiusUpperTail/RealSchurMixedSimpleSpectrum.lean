import SpectralRadiusUpperTail.RealGaussianSimpleSpectrum
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- The universal collision polynomial for an arbitrary finite matrix
index, including the dependent-sum indices of mixed real-Schur blocks. -/
noncomputable def finiteRealMatrixCollisionPolynomial
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    MvPolynomial (ι × ι) ℝ :=
  (Matrix.charpoly.univ ℝ ι).resultant
    (Matrix.charpoly.univ ℝ ι).derivative
      (Fintype.card ι) (Fintype.card ι - 1)

theorem finiteRealMatrixCollisionPolynomial_eval
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (A : (ι × ι) → ℝ) :
    MvPolynomial.eval A (finiteRealMatrixCollisionPolynomial ι) =
      (Matrix.of A.curry).charpoly.resultant
        (Matrix.of A.curry).charpoly.derivative
          (Fintype.card ι) (Fintype.card ι - 1) := by
  unfold finiteRealMatrixCollisionPolynomial
  change (MvPolynomial.eval₂Hom (RingHom.id ℝ) A) _ = _
  rw [← Polynomial.resultant_map_map (Matrix.charpoly.univ ℝ ι)
    (Matrix.charpoly.univ ℝ ι).derivative
    (Fintype.card ι) (Fintype.card ι - 1)
    (MvPolynomial.eval₂Hom (RingHom.id ℝ) A), ← Polynomial.derivative_map]
  have hmap : Polynomial.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) A)
      (Matrix.charpoly.univ ℝ ι) = (Matrix.of A.curry).charpoly :=
    Matrix.charpoly.univ_map_eval₂Hom ι (RingHom.id ℝ) A
  rw [hmap]

theorem finiteRealMatrixCollisionPolynomial_eval_ne_zero_iff
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (A : (ι × ι) → ℝ) :
    MvPolynomial.eval A (finiteRealMatrixCollisionPolynomial ι) ≠ 0 ↔
      (Matrix.of A.curry).charpoly.Separable := by
  rw [finiteRealMatrixCollisionPolynomial_eval ι A]
  simpa only [isUnit_iff_ne_zero, Polynomial.separable_def,
    Polynomial.natDegree_derivative, Matrix.charpoly_natDegree_eq_dim] using
    (Polynomial.isUnit_resultant_iff_isCoprime
      (f := (Matrix.of A.curry).charpoly)
      (g := (Matrix.of A.curry).charpoly.derivative)
      (Matrix.charpoly_monic (Matrix.of A.curry)))

theorem finiteRealMatrix_diagonal_distinct_charpoly_separable
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    ∃ d : ι → ℝ, (Matrix.diagonal d).charpoly.Separable := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivOfCardEq (by simp)
  let d : ι → ℝ := fun i => ((e i).val : ℝ)
  refine ⟨d, ?_⟩
  rw [Matrix.charpoly_diagonal, Polynomial.separable_prod_X_sub_C_iff]
  intro i j hij
  apply e.injective
  apply Fin.ext
  change (((e i).val : ℝ) = ((e j).val : ℝ)) at hij
  exact_mod_cast hij

theorem finiteRealMatrixCollisionPolynomial_ne_zero
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    finiteRealMatrixCollisionPolynomial ι ≠ 0 := by
  obtain ⟨d,hd⟩ := finiteRealMatrix_diagonal_distinct_charpoly_separable ι
  let A : (ι × ι) → ℝ := fun ij => Matrix.diagonal d ij.1 ij.2
  have hA : Matrix.of A.curry = Matrix.diagonal d := rfl
  have hn : MvPolynomial.eval A (finiteRealMatrixCollisionPolynomial ι) ≠ 0 :=
    (finiteRealMatrixCollisionPolynomial_eval_ne_zero_iff ι A).mpr (by
      rw [hA]
      exact hd)
  intro hzero
  exact hn (by rw [hzero, map_zero])

/-- The repeated-root locus is Lebesgue-null for every finite real
matrix-entry index, including a mixed-block dependent sum. -/
theorem finiteRealMatrix_charpoly_separable_ae_volume
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    ∀ᵐ A : (ι × ι) → ℝ, (Matrix.of A.curry).charpoly.Separable := by
  have h := mvPolynomial_eval_ne_zero_ae_pi
    (fun _ : ι × ι => (volume : Measure ℝ))
    (finiteRealMatrixCollisionPolynomial ι)
    (finiteRealMatrixCollisionPolynomial_ne_zero ι)
  filter_upwards [h] with A hA
  exact (finiteRealMatrixCollisionPolynomial_eval_ne_zero_iff ι A).mp hA

#print axioms finiteRealMatrix_charpoly_separable_ae_volume
end SpectralRadiusUpperTail
