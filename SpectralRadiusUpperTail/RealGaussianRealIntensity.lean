import SpectralRadiusUpperTail.RealLabelIntensity
import SpectralRadiusUpperTail.RealGaussianFixedSchurCountExpectation

namespace SpectralRadiusUpperTail
open MeasureTheory Classical
open scoped ENNReal BigOperators

noncomputable def realGaussianNormalizedSpectrum (n : ℕ)
    (a : (Fin n × Fin n) → ℝ) (i : Fin n) : ℂ :=
  (((1/Real.sqrt (n : ℝ)) : ℝ) : ℂ) * realGaussianMeasurableRawSpectrum n a i

theorem realGaussianNormalizedSpectrum_measurable (n : ℕ) (i : Fin n) :
    Measurable (fun a => realGaussianNormalizedSpectrum n a i) :=
  measurable_const.mul ((measurable_pi_apply i).comp
    (realGaussianMeasurableRawSpectrum_measurable n))

/-- The finite expected counting measure of the real normalized Gaussian
eigenvalues, defined from actual measurable spectral labels. -/
noncomputable def realGaussianRealIntensity (n : ℕ) : Measure ℝ :=
  realLabelIntensity (gaussianMatrixLaw n) n (realGaussianNormalizedSpectrum n)

instance realGaussianRealIntensity_isFiniteMeasure (n : ℕ) :
    IsFiniteMeasure (realGaussianRealIntensity n) := by
  unfold realGaussianRealIntensity
  infer_instance

theorem realGaussianRealIntensity_open_tail (n : ℕ) (hn : 0 < n) (b : ℝ) :
    realGaussianRealIntensity n (Set.Ioi b) =
      ENNReal.ofReal (∫ a, realGaussianExteriorCount n b 0 a ∂gaussianMatrixLaw n) := by
  rw [realGaussianRealIntensity, realLabelIntensity_open_tail _ _ _
    (realGaussianNormalizedSpectrum_measurable n),
    ← realGaussianExteriorCount_lintegral_eq_ofReal_expectation n hn b 0]
  apply lintegral_congr_ae
  filter_upwards [realGaussianMeasurableNormalizedSpectrum_roots_ae n hn] with a ha
  change (∑ i : Fin n,
    if (realGaussianNormalizedSpectrum n a i).im = 0 ∧
      b < (realGaussianNormalizedSpectrum n a i).re then (1 : ℝ≥0∞) else 0) =
    ENNReal.ofReal ((((((1/Real.sqrt (n : ℝ)) • Matrix.of a.curry).map
      Complex.ofRealHom).charpoly.roots.countP
        (fun z : ℂ => z.im = 0 ∧ b < z.re) : ℕ) : ℝ))
  rw [ha, Multiset.countP_map]
  change _ = ENNReal.ofReal (((Finset.univ.filter (fun i : Fin n =>
    (realGaussianNormalizedSpectrum n a i).im = 0 ∧
      b < (realGaussianNormalizedSpectrum n a i).re)).card : ℕ) : ℝ)
  simp only [Finset.sum_boole, ENNReal.ofReal_natCast]

#print axioms realGaussianNormalizedSpectrum_measurable
#print axioms realGaussianRealIntensity_isFiniteMeasure
#print axioms realGaussianRealIntensity_open_tail
end SpectralRadiusUpperTail
