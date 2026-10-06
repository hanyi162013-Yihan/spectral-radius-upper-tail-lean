import SpectralRadiusUpperTail.GaussianMarkedRealAnalyticMass
import SpectralRadiusUpperTail.ThreeCountEventRateFromAnalytic
import SpectralRadiusUpperTail.RealGaussianRadiusTwoCountInputs
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- The marked-eigenline identity for positive real roots, together with
the nonreal one-point upper bound, suffices for the real-Gaussian spectral
radius right-tail rate. The first identity is *not* proved here: proving it
requires the global marked-eigenline change of variables. -/
theorem realGaussianRadius_rate_of_marked_line_and_nonreal_count
    (r : ℝ) (hr : 1 < r)
    (hPos : ∀ n, 3 ≤ n →
      (∫ x, realGaussianExteriorCount n r 0 x
        ∂gaussianMatrixLaw n) = gaussianMarkedRealTailMass n r)
    (hNonreal : ∀ n, 3 ≤ n →
      (∫ x, realGaussianExteriorCount n r 2 x
        ∂gaussianMatrixLaw n) ≤
        2*realGinibreNonrealExteriorMass n r) :
    Tendsto (fun n : ℕ => Real.log ((gaussianMatrixLaw n).real
      {x | r < realMatrixRadius
        ((1/Real.sqrt (n : ℝ)) • entryMatrix x)})/(n : ℝ))
      atTop (𝓝 (-rate 1 r)) := by
  have hMeas (n : ℕ) (hn : 3 ≤ n) (i : Fin 3) :
      AEMeasurable (realGaussianExteriorCount n r i)
        (gaussianMatrixLaw n) :=
    realGaussianExteriorCount_aemeasurable n (by omega) r i
  have hInt (n : ℕ) (hn : 3 ≤ n) (i : Fin 3) :
      Integrable (realGaussianExteriorCount n r i)
        (gaussianMatrixLaw n) := by
    apply Integrable.of_bound (hMeas n hn i).aestronglyMeasurable (n : ℝ)
    filter_upwards [] with x
    obtain ⟨h0, _, htop⟩ := realGaussianExteriorCount_bounds n r i x
    simpa [Real.norm_eq_abs, abs_of_nonneg h0] using htop
  apply three_count_event_rate_from_analytic
    (fun n => (Fin n × Fin n) → ℝ) gaussianMatrixLaw
    (fun n i => realGaussianExteriorCount n r i)
    (fun n => {x | r < realMatrixRadius
      ((1/Real.sqrt (n : ℝ)) • entryMatrix x)})
    (fun n => gaussianMarkedRealTailMass n r)
    (fun n => realGinibreNonrealExteriorMass n r)
    (-rate 1 r)
    hMeas hInt
  · intro n i x
    exact (realGaussianExteriorCount_bounds n r i x).1
  · intro n i x
    exact (realGaussianExteriorCount_bounds n r i x).2.1
  · intro n i x
    exact (realGaussianExteriorCount_bounds n r i x).2.2
  · intro n hn x hx
    exact (realGaussianExteriorCount_cover n (by omega) r x).mpr (Or.inl hx)
  · intro n hn x hx
    have h := (realGaussianExteriorCount_cover n (by omega) r x).mp hx
    rcases h with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  · exact hPos
  · intro n hn
    rw [realGaussianRealRootCountExpectations_equal_ae n r
      (hMeas n hn 0)]
    exact hPos n hn
  · exact hNonreal
  · filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
    exact gaussianMarkedRealTailMass_pos n (by omega) r hr
  · exact Filter.Eventually.of_forall (fun n =>
      realGinibreNonrealExteriorMass_nonneg n r hr)
  · exact gaussianMarkedRealTailMass_log_rate r hr
  · exact gaussianMarkedRealPlusNonrealMass_log_rate r hr

#print axioms realGaussianRadius_rate_of_marked_line_and_nonreal_count
end SpectralRadiusUpperTail
