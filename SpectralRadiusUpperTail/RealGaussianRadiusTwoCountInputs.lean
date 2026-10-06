import SpectralRadiusUpperTail.RealGaussianRadiusFromOnePointAE
import SpectralRadiusUpperTail.RealGaussianRootCountSignSymmetry
import SpectralRadiusUpperTail.RealGaussianExteriorCountsAE
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- Gaussian sign symmetry identifies the two real-root count expectations
using only almost-everywhere measurability of the positive count. -/
theorem realGaussianRealRootCountExpectations_equal_ae
    (n : ℕ) (r : ℝ)
    (hPos : AEMeasurable (realGaussianExteriorCount n r 0)
      (gaussianMatrixLaw n)) :
    (∫ x, realGaussianExteriorCount n r 1 x ∂gaussianMatrixLaw n) =
    (∫ x, realGaussianExteriorCount n r 0 x ∂gaussianMatrixLaw n) := by
  let μ := gaussianMatrixLaw n
  have hmap : μ.map (fun x : (Fin n × Fin n) → ℝ => -x) = μ :=
    gaussianMatrixLaw_map_neg n
  have hPosMap : AEStronglyMeasurable
      (realGaussianExteriorCount n r 0)
      (μ.map (fun x : (Fin n × Fin n) → ℝ => -x)) := by
    rw [hmap]
    exact hPos.aestronglyMeasurable
  calc
    (∫ x, realGaussianExteriorCount n r 1 x ∂μ) =
        ∫ x, realGaussianExteriorCount n r 0 (-x) ∂μ := by
      congr 1
      funext x
      exact (realGaussianPositiveRootCount_neg n r x).symm
    _ = ∫ x, realGaussianExteriorCount n r 0 x
        ∂(μ.map (fun x : (Fin n × Fin n) → ℝ => -x)) := by
      exact (integral_map (by fun_prop) hPosMap).symm
    _ = _ := by rw [hmap]

/-- The actual real Gaussian radius right-tail rate, conditional solely on
two finite-dimensional one-point count identities. Measurability,
integrability, negative-root symmetry, and the first-moment LDP transfer
are all proved rather than assumed. -/
theorem realGaussianRadius_rate_of_two_count_inputs
    (r : ℝ) (hr : 1 < r)
    (hPos : ∀ n, 3 ≤ n →
      (∫ x, realGaussianExteriorCount n r 0 x
        ∂gaussianMatrixLaw n) = realGinibreRealPositiveTailMass n r)
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
  apply real_gaussian_radius_rate_from_one_point_ae
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
  · intro n hn
    rw [realGaussianRealRootCountExpectations_equal_ae n r
      (hMeas n hn 0)]
    exact hPos n hn
  · exact hNonreal

#print axioms realGaussianRealRootCountExpectations_equal_ae
#print axioms realGaussianRadius_rate_of_two_count_inputs
end SpectralRadiusUpperTail
