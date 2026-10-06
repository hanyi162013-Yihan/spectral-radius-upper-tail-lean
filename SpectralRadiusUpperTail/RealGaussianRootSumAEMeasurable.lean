import SpectralRadiusUpperTail.RealGaussianMeasurableRoots
import SpectralRadiusUpperTail.MatrixExteriorRootPowerPartition
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- A Borel weight summed over all normalized characteristic roots is
almost-everywhere measurable for an actual real Gaussian matrix. -/
theorem realGaussian_normalized_rootSum_aemeasurable
    (n : ℕ) (hn : 0 < n) (w : ℂ → ℝ) (hw : Measurable w) :
    AEMeasurable
      (fun x : (Fin n × Fin n) → ℝ =>
        (((1/Real.sqrt (n : ℝ)) • Matrix.of x.curry).map
          Complex.ofRealHom).charpoly.roots.map w |>.sum)
      (gaussianMatrixLaw n) := by
  classical
  let c : ℂ := (((1/Real.sqrt (n : ℝ)) : ℝ) : ℂ)
  let f : ((Fin n × Fin n) → ℝ) → ℝ :=
    fun x => ∑ i : Fin n,
      w (c*realGaussianMeasurableRawSpectrum n x i)
  have hf : Measurable f := by
    apply Finset.measurable_sum
    intro i hi
    exact hw.comp (measurable_const.mul
      ((measurable_pi_apply i).comp
        (realGaussianMeasurableRawSpectrum_measurable n)))
  apply hf.aemeasurable.congr
  filter_upwards [realGaussianMeasurableNormalizedSpectrum_roots_ae n hn]
    with x hx
  change f x = _
  rw [hx]
  simp [f, c, List.sum_ofFn]

#print axioms realGaussian_normalized_rootSum_aemeasurable
end SpectralRadiusUpperTail
