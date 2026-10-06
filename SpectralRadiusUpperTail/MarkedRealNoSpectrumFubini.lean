import SpectralRadiusUpperTail.MarkedRealDiagonalNoSpectrumWeight
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix BigOperators

private theorem markedRealNoSpectrum_det_continuous (m : ℕ) :
    Continuous (fun z : ℝ × ((Fin m × Fin m) → ℝ) =>
      (Matrix.of z.2.curry - z.1 •
        (1 : Matrix (Fin m) (Fin m) ℝ)).det) := by
  apply Continuous.matrix_det
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases hij : i = j
  · simp only [Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, if_pos hij]
    change Continuous (fun z : ℝ × ((Fin m × Fin m) → ℝ) =>
      z.2 (i,j) - z.1 * 1)
    fun_prop
  · simp only [Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, if_neg hij]
    change Continuous (fun z : ℝ × ((Fin m × Fin m) → ℝ) =>
      z.2 (i,j) - z.1 * 0)
    fun_prop

private theorem markedRealNoSpectrum_energy_continuous (m : ℕ) :
    Continuous (fun z : ℝ × ((Fin m × Fin m) → ℝ) =>
      z.1^2 + ∑ ij : Fin m × Fin m, (z.2 ij)^2) := by
  fun_prop

theorem markedRealNoSpectrumDiagonalWeight_measurable
    (m : ℕ) (b : ℝ) :
    Measurable (markedRealNoSpectrumDiagonalWeight m b) := by
  have hset : MeasurableSet
      {z : ℝ × ((Fin m × Fin m) → ℝ) | b < z.1} := by
    exact (isOpen_lt continuous_const continuous_fst).measurableSet
  have hdet : Measurable (fun z : ℝ × ((Fin m × Fin m) → ℝ) =>
      ENNReal.ofReal
        |(Matrix.of z.2.curry - z.1 •
          (1 : Matrix (Fin m) (Fin m) ℝ)).det|) :=
    (markedRealNoSpectrum_det_continuous m).abs.measurable.ennreal_ofReal
  have hgauss : Measurable (fun z : ℝ × ((Fin m × Fin m) → ℝ) =>
      ENNReal.ofReal
        (Real.exp (-(z.1^2 +
          ∑ ij : Fin m × Fin m, (z.2 ij)^2)/2))) :=
    (Real.continuous_exp.comp
      ((markedRealNoSpectrum_energy_continuous m).neg.div_const 2)).measurable.ennreal_ofReal
  unfold markedRealNoSpectrumDiagonalWeight
  exact Measurable.ite hset
    (hdet.mul (hgauss.mul measurable_const))
    measurable_const

/-- Tonelli makes the remaining kernel an outer scalar integral of a
Gaussian complementary-matrix integral. -/
theorem markedRealNoSpectrumDiagonalWeight_lintegral_prod
    (m : ℕ) (b : ℝ) :
    (∫⁻ z : ℝ × ((Fin m × Fin m) → ℝ),
      markedRealNoSpectrumDiagonalWeight m b z) =
      ∫⁻ x : ℝ, ∫⁻ a : (Fin m × Fin m) → ℝ,
        markedRealNoSpectrumDiagonalWeight m b (x,a) := by
  rw [Measure.volume_eq_prod ℝ ((Fin m × Fin m) → ℝ)]
  exact lintegral_prod
    (markedRealNoSpectrumDiagonalWeight m b)
    (markedRealNoSpectrumDiagonalWeight_measurable m b).aemeasurable

#print axioms markedRealNoSpectrumDiagonalWeight_lintegral_prod
end SpectralRadiusUpperTail
