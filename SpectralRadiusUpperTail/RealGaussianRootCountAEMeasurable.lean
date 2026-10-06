import SpectralRadiusUpperTail.RealGaussianMeasurableRoots
import SpectralRadiusUpperTail.RealGaussianRootCountInterface
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- Every Borel test on the normalized characteristic roots gives an
almost-everywhere measurable root count under the actual real Gaussian
matrix law. The finite count is represented by a measurable sum over the
Schur atlas labels on the simple-spectrum locus. -/
theorem realGaussian_normalized_rootCount_aemeasurable
    (n : ℕ) (hn : 0 < n) (p : ℂ → Prop) [DecidablePred p]
    (hp : MeasurableSet {z : ℂ | p z}) :
    AEMeasurable
      (fun x : (Fin n × Fin n) → ℝ =>
        (((((1/Real.sqrt (n : ℝ)) • Matrix.of x.curry).map
          Complex.ofRealHom).charpoly.roots.countP p : ℕ) : ℝ))
      (gaussianMatrixLaw n) := by
  classical
  let c : ℂ := (((1/Real.sqrt (n : ℝ)) : ℝ) : ℂ)
  let f : ((Fin n × Fin n) → ℝ) → ℝ :=
    fun x => ∑ i : Fin n,
      if p (c*realGaussianMeasurableRawSpectrum n x i)
      then (1 : ℝ) else 0
  have hf : Measurable f := by
    apply Finset.measurable_sum
    intro i hi
    have hg : Measurable
        (fun x : (Fin n × Fin n) → ℝ =>
          c*realGaussianMeasurableRawSpectrum n x i) :=
      measurable_const.mul
        ((measurable_pi_apply i).comp
          (realGaussianMeasurableRawSpectrum_measurable n))
    exact Measurable.ite (hg hp) measurable_const measurable_const
  apply hf.aemeasurable.congr
  filter_upwards [realGaussianMeasurableNormalizedSpectrum_roots_ae n hn]
    with x hx
  change f x = (((((1/Real.sqrt (n : ℝ)) • Matrix.of x.curry).map
      Complex.ofRealHom).charpoly.roots.countP p : ℕ) : ℝ)
  rw [hx, Multiset.countP_map]
  change f x = (((Finset.univ.filter
    (fun i : Fin n => p (c*realGaussianMeasurableRawSpectrum n x i))).card : ℕ) : ℝ)
  simpa only [f, Finset.sum_boole]

#print axioms realGaussian_normalized_rootCount_aemeasurable
end SpectralRadiusUpperTail
