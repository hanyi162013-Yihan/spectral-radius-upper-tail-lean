import SpectralRadiusUpperTail.RealArrayGaussianDensity

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal BigOperators

/-- Gaussian entry-array measures factor across native blocks, even
when the blocks have different finite dimensions. -/
theorem realArrayGaussianMeasure_pi {ι : Type*} [Fintype ι]
    (κ : ι → Type*) [∀ i, Fintype (κ i)] (n : ℝ) (hn : 0 < n) :
    Measure.pi (fun i => realArrayGaussianMeasure (ι := κ i) n) =
      (volume : Measure ((i : ι) → κ i → ℝ)).withDensity
        (fun A => ENNReal.ofReal (∏ i, Real.exp (-(n/2)*∑ j : κ i, (A i j)^2))) := by
  rw [volume_pi,dependent_pi_withDensity_ofReal
    (fun i => (volume : Measure (κ i → ℝ)))
    (fun i A => Real.exp (-(n/2)*∑ j : κ i, (A j)^2))
    (fun _ => realArrayGaussianWeight_integrable n hn)
    (fun _ _ => (Real.exp_pos _).le)]
  rfl

theorem realArrayGaussianMeasure_pi_lintegral {ι : Type*} [Fintype ι]
    (κ : ι → Type*) [∀ i, Fintype (κ i)] (n : ℝ) (hn : 0 < n)
    (H : ((i : ι) → κ i → ℝ) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ A, H A ∂Measure.pi (fun i => realArrayGaussianMeasure (ι := κ i) n)) =
      ∫⁻ A, ENNReal.ofReal (∏ i, Real.exp (-(n/2)*∑ j : κ i, (A i j)^2))*H A := by
  rw [realArrayGaussianMeasure_pi κ n hn]
  apply lintegral_withDensity_eq_lintegral_mul _ _ hH
  fun_prop

#print axioms realArrayGaussianMeasure_pi
#print axioms realArrayGaussianMeasure_pi_lintegral
end SpectralRadiusUpperTail
