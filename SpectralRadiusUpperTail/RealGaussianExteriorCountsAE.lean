import SpectralRadiusUpperTail.RealGaussianRootCountAEMeasurable
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- The three exterior characteristic-root counts used by the real
Gaussian radius argument are almost-everywhere measurable. -/
theorem realGaussianExteriorCount_aemeasurable
    (n : ℕ) (hn : 0 < n) (r : ℝ) (i : Fin 3) :
    AEMeasurable (realGaussianExteriorCount n r i)
      (gaussianMatrixLaw n) := by
  classical
  have hReal : MeasurableSet {z : ℂ | z.im = 0} := by measurability
  have hPos : MeasurableSet {z : ℂ | r < z.re} :=
    measurableSet_lt measurable_const Complex.continuous_re.measurable
  have hNeg : MeasurableSet {z : ℂ | z.re < -r} :=
    measurableSet_lt Complex.continuous_re.measurable measurable_const
  have hNon : MeasurableSet {z : ℂ | z.im ≠ 0} := by
    convert hReal.compl using 1
    ext z
    simp
  have hRad : MeasurableSet {z : ℂ | r < ‖z‖} :=
    measurableSet_lt measurable_const measurable_norm
  fin_cases i
  · change AEMeasurable
      (fun x : (Fin n × Fin n) → ℝ =>
        (((((1/Real.sqrt (n : ℝ)) • Matrix.of x.curry).map
          Complex.ofRealHom).charpoly.roots.countP
          (fun z : ℂ => z.im = 0 ∧ r < z.re) : ℕ) : ℝ))
      (gaussianMatrixLaw n)
    exact realGaussian_normalized_rootCount_aemeasurable n hn
      (fun z : ℂ => z.im = 0 ∧ r < z.re) (hReal.inter hPos)
  · change AEMeasurable
      (fun x : (Fin n × Fin n) → ℝ =>
        (((((1/Real.sqrt (n : ℝ)) • Matrix.of x.curry).map
          Complex.ofRealHom).charpoly.roots.countP
          (fun z : ℂ => z.im = 0 ∧ z.re < -r) : ℕ) : ℝ))
      (gaussianMatrixLaw n)
    exact realGaussian_normalized_rootCount_aemeasurable n hn
      (fun z : ℂ => z.im = 0 ∧ z.re < -r) (hReal.inter hNeg)
  · change AEMeasurable
      (fun x : (Fin n × Fin n) → ℝ =>
        (((((1/Real.sqrt (n : ℝ)) • Matrix.of x.curry).map
          Complex.ofRealHom).charpoly.roots.countP
          (fun z : ℂ => z.im ≠ 0 ∧ r < ‖z‖) : ℕ) : ℝ))
      (gaussianMatrixLaw n)
    exact realGaussian_normalized_rootCount_aemeasurable n hn
      (fun z : ℂ => z.im ≠ 0 ∧ r < ‖z‖) (hNon.inter hRad)

#print axioms realGaussianExteriorCount_aemeasurable
end SpectralRadiusUpperTail
