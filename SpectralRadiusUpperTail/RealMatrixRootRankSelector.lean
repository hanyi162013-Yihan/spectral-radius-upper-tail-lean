import SpectralRadiusUpperTail.RealRootRankMeasurable
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- A globally measurable label count, equal to real-root rank at every
simple-spectrum matrix. The measurable labels come from the complex Schur
atlas; the arbitrary values off the simple locus are harmless. -/
noncomputable def realMatrixRootRankSelector (n : ℕ) :
    (((Fin n × Fin n) → ℝ) × ℝ) → ℕ :=
  fun p => ∑ i : Fin n,
    if (realGaussianMeasurableRawSpectrum n p.1 i).im = 0 ∧
        (realGaussianMeasurableRawSpectrum n p.1 i).re < p.2
    then 1 else 0

theorem realMatrixRootRankSelector_measurable (n : ℕ) :
    Measurable (realMatrixRootRankSelector n) := by
  unfold realMatrixRootRankSelector
  apply Finset.measurable_sum
  intro i hi
  have hspec : Measurable
      (fun p : (((Fin n × Fin n) → ℝ) × ℝ) =>
        realGaussianMeasurableRawSpectrum n p.1 i) :=
    ((measurable_pi_apply i).comp
      (realGaussianMeasurableRawSpectrum_measurable n)).comp measurable_fst
  have him : Measurable (fun p : (((Fin n × Fin n) → ℝ) × ℝ) =>
      (realGaussianMeasurableRawSpectrum n p.1 i).im) :=
    Complex.continuous_im.measurable.comp hspec
  have hre : Measurable (fun p : (((Fin n × Fin n) → ℝ) × ℝ) =>
      (realGaussianMeasurableRawSpectrum n p.1 i).re) :=
    Complex.continuous_re.measurable.comp hspec
  have hset : MeasurableSet
      {p : (((Fin n × Fin n) → ℝ) × ℝ) |
        (realGaussianMeasurableRawSpectrum n p.1 i).im = 0 ∧
          (realGaussianMeasurableRawSpectrum n p.1 i).re < p.2} :=
    (measurableSet_eq_fun him measurable_const).inter
      (measurableSet_lt hre measurable_snd)
  exact Measurable.ite hset measurable_const measurable_const

theorem realMatrixRootRankSelector_eq_of_separable
    (n : ℕ) (x : (Fin n × Fin n) → ℝ) (t : ℝ)
    (hx : (Matrix.of x.curry).charpoly.Separable) :
    realMatrixRootRankSelector n (x,t) =
      realPolynomialRootRank (Matrix.of x.curry).charpoly t := by
  exact (realMatrixRootRank_eq_measurableSpectrumCount n x t hx).symm

#print axioms realMatrixRootRankSelector_measurable
#print axioms realMatrixRootRankSelector_eq_of_separable
end SpectralRadiusUpperTail
