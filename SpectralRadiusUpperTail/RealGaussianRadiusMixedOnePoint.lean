import SpectralRadiusUpperTail.RealGaussianRadiusUpperHalfWeighted
import SpectralRadiusUpperTail.RealGaussianRootCountInterface
import SpectralRadiusUpperTail.RealGinibreRealTailRate
import SpectralRadiusUpperTail.RealGinibreAnalyticTailMass
import SpectralRadiusUpperTail.PositiveCountSandwich
import SpectralRadiusUpperTail.PositiveCountSandwichAE
import SpectralRadiusUpperTail.FirstMomentExponentialTransfer
import SpectralRadiusUpperTail.RealGaussianExteriorCountsAE
import SpectralRadiusUpperTail.RealGaussianSubstatIntegrable
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Filter Set
open scoped Topology

/-- A mixed finite-dimensional one-point route to the real Gaussian radius
right-tail LDP. The lower bound uses only the positive-real root count; the
upper bound uses positive-real and upper-half-plane weighted root powers.
No conditional Schur distribution or nonreal count formula is assumed. -/
theorem realGaussianRadius_rate_of_mixed_onePoint
    (r : ℝ) (hr : 1 < r)
    (hPosCount : ∀ n, 3 ≤ n →
      (∫ x, realGaussianExteriorCount n r 0 x
        ∂gaussianMatrixLaw n) = realGinibreRealPositiveTailMass n r)
    (hPosPower : ∀ n k, 3 ≤ n →
      (∫ x, realGaussianPositiveRealExteriorPower n k x
        ∂gaussianMatrixLaw n) ≤
        (∫ x in Ioi (1 : ℝ),
          x^(2*k)*realGinibreFirstDensity n x) +
        (∫ x in Ioi (1 : ℝ),
          x^(2*k)*realGinibreDominantDensity n x))
    (hUpperPower : ∀ n k, 3 ≤ n →
      2*(∫ x, realGaussianUpperNonrealExteriorPower n k x
        ∂gaussianMatrixLaw n) ≤
        (∫ z : ℂ in {z | 1 < ‖z‖},
          ‖z‖^(2*k)*realGinibreNonrealDensityAt n z)) :
    Tendsto (fun n : ℕ => Real.log ((gaussianMatrixLaw n).real
      {x | r < realMatrixRadius
        ((1/Real.sqrt (n : ℝ)) • entryMatrix x)})/(n : ℝ))
      atTop (𝓝 (-rate 1 r)) := by
  have hInt (n : ℕ) (hn : 3 ≤ n) :
      Integrable (realGaussianExteriorCount n r 0)
        (gaussianMatrixLaw n) := by
    apply Integrable.of_bound
      ((realGaussianExteriorCount_aemeasurable n (by omega) r 0).aestronglyMeasurable)
      (n : ℝ)
    filter_upwards [] with x
    obtain ⟨h0, _, hn⟩ := realGaussianExteriorCount_bounds n r 0 x
    simpa [Real.norm_eq_abs, abs_of_nonneg h0] using hn
  have hLow : ∀ᶠ n : ℕ in atTop,
      realGinibreRealPositiveTailMass n r/(n : ℝ) ≤
        (gaussianMatrixLaw n).real
          {x | r < realMatrixRadius
            ((1/Real.sqrt (n : ℝ)) • entryMatrix x)} := by
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
    have hnpos : 0 < n := by omega
    have hcount := positive_count_probability_sandwich_ae
      (gaussianMatrixLaw n) (realGaussianExteriorCount n r 0)
      (realGaussianExteriorCount_aemeasurable n hnpos r 0)
      (hInt n hn) (n : ℝ)
      (fun x => (realGaussianExteriorCount_bounds n r 0 x).1)
      (fun x => (realGaussianExteriorCount_bounds n r 0 x).2.1)
      (fun x => (realGaussianExteriorCount_bounds n r 0 x).2.2)
    have hsub : {x | 0 < realGaussianExteriorCount n r 0 x} ⊆
        {x | r < realMatrixRadius
          ((1/Real.sqrt (n : ℝ)) • entryMatrix x)} := by
      intro x hx
      exact (realGaussianExteriorCount_cover n hnpos r x).mpr (Or.inl hx)
    calc
      realGinibreRealPositiveTailMass n r/(n : ℝ) =
          (∫ x, realGaussianExteriorCount n r 0 x
            ∂gaussianMatrixLaw n)/(n : ℝ) := by rw [hPosCount n hn]
      _ ≤ (gaussianMatrixLaw n).real
          {x | 0 < realGaussianExteriorCount n r 0 x} := by
        exact (div_le_iff₀ (Nat.cast_pos.mpr hnpos)).2
          (by simpa [mul_comm] using hcount.1)
      _ ≤ _ := measureReal_mono hsub
  have hUpper : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (gaussianMatrixLaw n).real
        {x | r < realMatrixRadius
          ((1/Real.sqrt (n : ℝ)) • entryMatrix x)} ≤
        Real.exp ((n : ℝ)*(-rate 1 r+ε)) := by
    intro ε hε
    filter_upwards [realGaussianRadius_upper_of_two_weighted_classes
      (fun n k hn => realGaussianPositiveRealExteriorPower_integrable
        n k (by omega))
      (fun n k hn => realGaussianUpperNonrealExteriorPower_integrable
        n k (by omega))
      hPosPower hUpperPower r hr ε hε] with n hn
    have hsub : {x : (Fin n × Fin n) → ℝ | r < realMatrixRadius
        ((1/Real.sqrt (n : ℝ)) • entryMatrix x)} ⊆
        {x : (Fin n × Fin n) → ℝ | r ≤ realMatrixRadius
          ((1/Real.sqrt (n : ℝ)) • entryMatrix x)} := by
      intro x hx
      change r < realMatrixRadius
        ((1/Real.sqrt (n : ℝ)) • entryMatrix x) at hx
      exact le_of_lt hx
    exact (measureReal_mono (μ := gaussianMatrixLaw n) hsub).trans hn
  exact firstMomentLower_exponentialUpper_logRate
    (fun n => realGinibreRealPositiveTailMass n r)
    (fun n => (gaussianMatrixLaw n).real
      {x | r < realMatrixRadius
        ((1/Real.sqrt (n : ℝ)) • entryMatrix x)})
    (-rate 1 r)
    (by filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
        exact realGinibreRealPositiveTailMass_pos n hn r hr)
    (by simpa only [realGinibreRealPositiveTailMass] using
      realGinibreRealTail_log_rate r hr)
    hLow hUpper

#print axioms realGaussianRadius_rate_of_mixed_onePoint
end SpectralRadiusUpperTail
