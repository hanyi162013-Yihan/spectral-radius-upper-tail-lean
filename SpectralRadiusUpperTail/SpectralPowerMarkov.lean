import SpectralRadiusUpperTail.DominatedMatrixTail
import SpectralRadiusUpperTail.RealMomentClass

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- Reuse the existing finite spectral-tail comparison with the manuscript's
finiteness-aware even-moment class. No Gaussian asymptotic is assumed here. -/
theorem real_class_spectral_power_markov (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsym : μ.map (fun x : ℝ => -x) = μ) (h : GaussianEvenMomentDomination μ)
    (n k : ℕ) (hk : k ≠ 0) (r : ℝ) (hr : 0 < r) :
    (Measure.pi (fun _ : Fin n × Fin n => μ)).real
      {x | r ≤ realMatrixRadius ((1/Real.sqrt n) • entryMatrix x)} ≤
      (∫ x, scaledFrobeniusPowerSquared (1/Real.sqrt n) k x ∂gaussianMatrixLaw n)/r^(2*k) :=
  dominated_matrix_spectral_tail_le_moment (fun _ => μ) (fun _ => standardNormal)
    (fun _ => dominated_even_all_powers_integrable μ h)
    (fun _ => standardNormal_pow_integrable)
    (fun _ k => (symmetric_dominated_moments μ hsym h k).1)
    (fun _ k => (symmetric_dominated_moments μ hsym h k).2)
    (1/Real.sqrt n) r hr k hk

#print axioms real_class_spectral_power_markov
end SpectralRadiusUpperTail
