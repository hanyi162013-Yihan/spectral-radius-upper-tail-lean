import SpectralRadiusUpperTail.RealGaussianRootSumAEMeasurable
import SpectralRadiusUpperTail.RealGaussianUpperHalfPlanePower
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

theorem realGaussianExteriorRootPower_aemeasurable
    (n k : ℕ) (hn : 0 < n) :
    AEMeasurable (realGaussianExteriorRootPower n k)
      (gaussianMatrixLaw n) := by
  have hw : Measurable (fun z : ℂ =>
      if 1 < ‖z‖ then ‖z‖^(2*k) else (0 : ℝ)) :=
    Measurable.ite (measurableSet_lt measurable_const measurable_norm)
      (measurable_norm.pow_const _) measurable_const
  change AEMeasurable
    (fun x : (Fin n × Fin n) → ℝ =>
      (((1/Real.sqrt (n : ℝ)) • Matrix.of x.curry).map
        Complex.ofRealHom).charpoly.roots.map
          (fun z : ℂ => if 1 < ‖z‖ then ‖z‖^(2*k) else 0) |>.sum)
    (gaussianMatrixLaw n)
  exact realGaussian_normalized_rootSum_aemeasurable n hn _ hw

theorem realGaussianPositiveRealExteriorPower_aemeasurable
    (n k : ℕ) (hn : 0 < n) :
    AEMeasurable (realGaussianPositiveRealExteriorPower n k)
      (gaussianMatrixLaw n) := by
  have hp : MeasurableSet {z : ℂ | z.im = 0 ∧ 1 < z.re} := by
    have hReal : MeasurableSet {z : ℂ | z.im = 0} := by measurability
    exact hReal.inter
      (measurableSet_lt measurable_const Complex.continuous_re.measurable)
  have hw : Measurable (fun z : ℂ =>
      if z.im = 0 ∧ 1 < z.re then z.re^(2*k) else (0 : ℝ)) :=
    Measurable.ite hp (Complex.continuous_re.measurable.pow_const _)
      measurable_const
  change AEMeasurable
    (fun x : (Fin n × Fin n) → ℝ =>
      (((1/Real.sqrt (n : ℝ)) • Matrix.of x.curry).map
        Complex.ofRealHom).charpoly.roots.map
          (fun z : ℂ => if z.im = 0 ∧ 1 < z.re then z.re^(2*k) else 0) |>.sum)
    (gaussianMatrixLaw n)
  exact realGaussian_normalized_rootSum_aemeasurable n hn _ hw

theorem realGaussianUpperNonrealExteriorPower_aemeasurable
    (n k : ℕ) (hn : 0 < n) :
    AEMeasurable (realGaussianUpperNonrealExteriorPower n k)
      (gaussianMatrixLaw n) := by
  have hp : MeasurableSet {z : ℂ | 0 < z.im ∧ 1 < ‖z‖} :=
    (measurableSet_lt measurable_const Complex.continuous_im.measurable).inter
      (measurableSet_lt measurable_const measurable_norm)
  have hw : Measurable (fun z : ℂ =>
      if 0 < z.im ∧ 1 < ‖z‖ then ‖z‖^(2*k) else (0 : ℝ)) :=
    Measurable.ite hp (measurable_norm.pow_const _) measurable_const
  change AEMeasurable
    (fun x : (Fin n × Fin n) → ℝ =>
      (((1/Real.sqrt (n : ℝ)) • Matrix.of x.curry).map
        Complex.ofRealHom).charpoly.roots.map
          (fun z : ℂ => if 0 < z.im ∧ 1 < ‖z‖ then ‖z‖^(2*k) else 0) |>.sum)
    (gaussianMatrixLaw n)
  exact realGaussian_normalized_rootSum_aemeasurable n hn _ hw

#print axioms realGaussianExteriorRootPower_aemeasurable
#print axioms realGaussianPositiveRealExteriorPower_aemeasurable
#print axioms realGaussianUpperNonrealExteriorPower_aemeasurable
end SpectralRadiusUpperTail
