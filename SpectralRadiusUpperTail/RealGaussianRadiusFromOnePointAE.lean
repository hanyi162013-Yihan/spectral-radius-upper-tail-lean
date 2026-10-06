import SpectralRadiusUpperTail.RealGinibreAnalyticTailMass
import SpectralRadiusUpperTail.ThreeCountEventSandwichAE
import SpectralRadiusUpperTail.FirstMomentTailTransfer
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- An independent right-tail LDP deduction from finite-dimensional
one-point count identities, requiring only almost-everywhere measurability
of the three root counts. -/
theorem real_gaussian_radius_rate_from_one_point_ae
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (C : ∀ n, Fin 3 → Ω n → ℝ) (E : ∀ n, Set (Ω n))
    (r : ℝ) (hr : 1 < r)
    (hC : ∀ n, 3 ≤ n → ∀ i, AEMeasurable (C n i) (P n))
    (hInt : ∀ n, 3 ≤ n → ∀ i, Integrable (C n i) (P n))
    (hzero : ∀ n i x, 0 ≤ C n i x)
    (hgap : ∀ n i x, 0 < C n i x → 1 ≤ C n i x)
    (hbound : ∀ n i x, C n i x ≤ (n : ℝ))
    (hlower : ∀ n, 3 ≤ n → {x | 0 < C n 0 x} ⊆ E n)
    (hupper : ∀ n, 3 ≤ n → E n ⊆ {x | 0 < C n 0 x} ∪
      {x | 0 < C n 1 x} ∪ {x | 0 < C n 2 x})
    (hrealPos : ∀ n, 3 ≤ n →
      (∫ x, C n 0 x ∂P n) = realGinibreRealPositiveTailMass n r)
    (hrealNeg : ∀ n, 3 ≤ n →
      (∫ x, C n 1 x ∂P n) = realGinibreRealPositiveTailMass n r)
    (hnonreal : ∀ n, 3 ≤ n →
      (∫ x, C n 2 x ∂P n) ≤ 2*realGinibreNonrealExteriorMass n r) :
    Tendsto (fun n : ℕ => Real.log ((P n).real (E n))/(n : ℝ))
      atTop (𝓝 (-rate 1 r)) := by
  have hcount (n : ℕ) (hn : 3 ≤ n) :
      (∫ x, C n 0 x ∂P n)/(n : ℝ) ≤ (P n).real (E n) ∧
      (P n).real (E n) ≤ (∫ x, C n 0 x ∂P n) +
        (∫ x, C n 1 x ∂P n) + (∫ x, C n 2 x ∂P n) := by
    exact three_count_event_sandwich_ae (P n) (C n)
      (hC n hn) (hInt n hn) (n : ℝ)
      (Nat.cast_pos.mpr (by omega)) (hzero n) (hgap n)
      (hbound n) (E n) (hlower n hn) (hupper n hn)
  have haPos : ∀ᶠ n : ℕ in atTop,
      0 < realGinibreRealPositiveTailMass n r := by
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
    exact realGinibreRealPositiveTailMass_pos n hn r hr
  have hbPos : ∀ᶠ n : ℕ in atTop,
      0 < realGinibreRealPositiveTailMass n r +
        realGinibreNonrealExteriorMass n r := by
    filter_upwards [haPos] with n hn
    exact add_pos_of_pos_of_nonneg hn
      (realGinibreNonrealExteriorMass_nonneg n r hr)
  have hlow : ∀ᶠ n : ℕ in atTop,
      realGinibreRealPositiveTailMass n r/(n : ℝ) ≤
        (P n).real (E n) := by
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
    simpa only [hrealPos n hn] using (hcount n hn).1
  have hupp : ∀ᶠ n : ℕ in atTop,
      (P n).real (E n) ≤
        2*(realGinibreRealPositiveTailMass n r +
          realGinibreNonrealExteriorMass n r) := by
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
    have hh := (hcount n hn).2
    rw [hrealPos n hn, hrealNeg n hn] at hh
    linarith [hnonreal n hn]
  exact first_moment_tail_transfer
    (fun n => realGinibreRealPositiveTailMass n r)
    (fun n => realGinibreRealPositiveTailMass n r +
      realGinibreNonrealExteriorMass n r)
    (fun n => (P n).real (E n)) (-rate 1 r)
    haPos hbPos
    (by simpa only [realGinibreRealPositiveTailMass] using
      realGinibreRealTail_log_rate r hr)
    (realGinibreAnalyticTailMass_log_rate r hr)
    hlow hupp

#print axioms real_gaussian_radius_rate_from_one_point_ae
end SpectralRadiusUpperTail
