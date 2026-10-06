import SpectralRadiusUpperTail.MarkedRealDiagonalSimpleSpectrum
import SpectralRadiusUpperTail.RealGaussianSimpleSpectrum
import SpectralRadiusUpperTail.RealPolynomialZeroSets
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set
open scoped Matrix

private theorem markedRealComplementSimple_measurableSet (m : ℕ) :
    MeasurableSet {a : (Fin m × Fin m) → ℝ |
      (Matrix.of a.curry).charpoly.Separable} := by
  have heq :
      {a : (Fin m × Fin m) → ℝ |
        (Matrix.of a.curry).charpoly.Separable} =
      {a | MvPolynomial.eval a (collisionPolynomial m) ≠ 0} := by
    ext a
    exact (collisionPolynomial_eval_ne_zero_iff m a).symm
  rw [heq]
  exact ((measurableSet_singleton 0).preimage
    (collisionPolynomial m).continuous_eval.measurable).compl

private theorem markedRealComplementEval_continuous (m : ℕ) :
    Continuous (fun z : ℝ × ((Fin m × Fin m) → ℝ) =>
      (Matrix.of z.2.curry).charpoly.eval z.1) := by
  have hmat : Continuous (fun z : ℝ × ((Fin m × Fin m) → ℝ) =>
      Matrix.scalar (Fin m) z.1 - Matrix.of z.2.curry) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    by_cases hij : i = j
    · simp only [Matrix.sub_apply, Matrix.scalar_apply,
        Matrix.diagonal_apply, if_pos hij]
      change Continuous (fun z : ℝ × ((Fin m × Fin m) → ℝ) =>
        z.1 - z.2 (i,j))
      fun_prop
    · simp only [Matrix.sub_apply, Matrix.scalar_apply,
        Matrix.diagonal_apply, if_neg hij]
      change Continuous (fun z : ℝ × ((Fin m × Fin m) → ℝ) =>
        0 - z.2 (i,j))
      fun_prop
  have h := hmat.matrix_det
  convert h using 1
  funext z
  exact Matrix.eval_charpoly (Matrix.of z.2.curry) z.1

/-- A Gaussian scalar and independent complementary matrix give a
simple two-block spectrum for almost every pair of Lebesgue coordinates. -/
theorem markedRealDiagonal_simpleSpectrum_ae_volume (m : ℕ) :
    ∀ᵐ z : ℝ × ((Fin m × Fin m) → ℝ),
      ((Polynomial.X - Polynomial.C z.1) *
        (Matrix.of z.2.curry).charpoly).Separable := by
  let p : ℝ × ((Fin m × Fin m) → ℝ) → Prop :=
    fun z => ((Polynomial.X - Polynomial.C z.1) *
      (Matrix.of z.2.curry).charpoly).Separable
  have hsimpleSet : MeasurableSet
      {z : ℝ × ((Fin m × Fin m) → ℝ) |
        (Matrix.of z.2.curry).charpoly.Separable} :=
    (markedRealComplementSimple_measurableSet m).preimage measurable_snd
  have hsimple : ∀ᵐ z ∂((volume : Measure ℝ).prod
      (volume : Measure ((Fin m × Fin m) → ℝ))),
      (Matrix.of z.2.curry).charpoly.Separable := by
    apply (Measure.ae_prod_iff_ae_ae hsimpleSet).2
    exact Filter.Eventually.of_forall
      (fun _ : ℝ => charpoly_separable_ae_volume m)
  have hevalSet : MeasurableSet
      {z : ℝ × ((Fin m × Fin m) → ℝ) |
        (Matrix.of z.2.curry).charpoly.eval z.1 ≠ 0} :=
    ((measurableSet_singleton 0).preimage
      (markedRealComplementEval_continuous m).measurable).compl
  have heval : ∀ᵐ z ∂((volume : Measure ℝ).prod
      (volume : Measure ((Fin m × Fin m) → ℝ))),
      (Matrix.of z.2.curry).charpoly.eval z.1 ≠ 0 := by
    apply (Measure.ae_prod_iff_ae_ae hevalSet).2
    apply (Measure.ae_ae_comm hevalSet).2
    exact Filter.Eventually.of_forall (fun a :
      (Fin m × Fin m) → ℝ =>
        polynomial_eval_ne_zero_ae volume
          (Matrix.of a.curry).charpoly
          (Matrix.of a.curry).charpoly_monic.ne_zero)
  rw [Measure.volume_eq_prod ℝ ((Fin m × Fin m) → ℝ)]
  filter_upwards [hsimple, heval] with z hs he
  exact markedRealDiagonal_product_separable m z.1
    (Matrix.of z.2.curry) hs he

#print axioms markedRealDiagonal_simpleSpectrum_ae_volume
end SpectralRadiusUpperTail
