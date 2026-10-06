import SpectralRadiusUpperTail.RealGaussianRadiusFromOnePoint
import SpectralRadiusUpperTail.RealGaussianRootCountInterface
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- The actual normalized real Gaussian matrix radius has the expected
right-tail rate once the finite-dimensional one-point identities and
root-count measurability are supplied. No Gaussian LDP is assumed. -/
theorem real_gaussian_radius_rate_of_one_point_identities
    (r : ℝ) (hr : 1 < r)
    (hMeas : ∀ n i, Measurable (realGaussianExteriorCount n r i))
    (hPos : ∀ n, 3 ≤ n →
      (∫ x, realGaussianExteriorCount n r 0 x ∂gaussianMatrixLaw n) =
        realGinibreRealPositiveTailMass n r)
    (hNeg : ∀ n, 3 ≤ n →
      (∫ x, realGaussianExteriorCount n r 1 x ∂gaussianMatrixLaw n) =
        realGinibreRealPositiveTailMass n r)
    (hNonreal : ∀ n, 3 ≤ n →
      (∫ x, realGaussianExteriorCount n r 2 x ∂gaussianMatrixLaw n) ≤
        2*realGinibreNonrealExteriorMass n r) :
    Tendsto (fun n : ℕ => Real.log ((gaussianMatrixLaw n).real
      {x | r < realMatrixRadius ((1/Real.sqrt (n : ℝ)) • entryMatrix x)}) /
      (n : ℝ)) atTop (𝓝 (-rate 1 r)) := by
  have hInt (n : ℕ) (i : Fin 3) :
      Integrable (realGaussianExteriorCount n r i) (gaussianMatrixLaw n) := by
    apply Integrable.of_bound (hMeas n i).aestronglyMeasurable (n : ℝ)
    filter_upwards [] with x
    obtain ⟨h0, _, hn⟩ := realGaussianExteriorCount_bounds n r i x
    simpa [Real.norm_eq_abs, abs_of_nonneg h0] using hn
  apply real_gaussian_radius_rate_from_one_point
    (fun n => (Fin n × Fin n) → ℝ) gaussianMatrixLaw
    (fun n i => realGaussianExteriorCount n r i)
    (fun n => {x | r < realMatrixRadius
      ((1/Real.sqrt (n : ℝ)) • entryMatrix x)})
    r hr hMeas hInt
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
  · exact hNeg
  · exact hNonreal

#print axioms real_gaussian_radius_rate_of_one_point_identities
end SpectralRadiusUpperTail
