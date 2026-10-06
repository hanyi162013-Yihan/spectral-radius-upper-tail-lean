import SpectralRadiusUpperTail.ThreeCountEventSandwichAE
import SpectralRadiusUpperTail.FirstMomentTailTransfer
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- A reusable first-moment transfer for three eigenvalue classes when
the positive and negative real classes have the same expected count. -/
theorem three_count_event_rate_from_analytic
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (C : ∀ n, Fin 3 → Ω n → ℝ) (E : ∀ n, Set (Ω n))
    (A B : ℕ → ℝ) (L : ℝ)
    (hC : ∀ n, 3 ≤ n → ∀ i, AEMeasurable (C n i) (P n))
    (hInt : ∀ n, 3 ≤ n → ∀ i, Integrable (C n i) (P n))
    (hzero : ∀ n i x, 0 ≤ C n i x)
    (hgap : ∀ n i x, 0 < C n i x → 1 ≤ C n i x)
    (hbound : ∀ n i x, C n i x ≤ (n : ℝ))
    (hlower : ∀ n, 3 ≤ n → {x | 0 < C n 0 x} ⊆ E n)
    (hupper : ∀ n, 3 ≤ n → E n ⊆ {x | 0 < C n 0 x} ∪
      {x | 0 < C n 1 x} ∪ {x | 0 < C n 2 x})
    (hrealPos : ∀ n, 3 ≤ n → (∫ x, C n 0 x ∂P n) = A n)
    (hrealNeg : ∀ n, 3 ≤ n → (∫ x, C n 1 x ∂P n) = A n)
    (hnonreal : ∀ n, 3 ≤ n → (∫ x, C n 2 x ∂P n) ≤ 2*B n)
    (hapos : ∀ᶠ n in atTop, 0 < A n)
    (hbnonneg : ∀ᶠ n in atTop, 0 ≤ B n)
    (hArate : Tendsto (fun n => Real.log (A n)/(n : ℝ)) atTop (𝓝 L))
    (hABrate : Tendsto (fun n => Real.log (A n+B n)/(n : ℝ)) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => Real.log ((P n).real (E n))/(n : ℝ))
      atTop (𝓝 L) := by
  have hcount (n : ℕ) (hn : 3 ≤ n) :
      (∫ x, C n 0 x ∂P n)/(n : ℝ) ≤ (P n).real (E n) ∧
      (P n).real (E n) ≤ (∫ x, C n 0 x ∂P n) +
        (∫ x, C n 1 x ∂P n) + (∫ x, C n 2 x ∂P n) := by
    exact three_count_event_sandwich_ae (P n) (C n)
      (hC n hn) (hInt n hn) (n : ℝ)
      (Nat.cast_pos.mpr (by omega)) (hzero n) (hgap n)
      (hbound n) (E n) (hlower n hn) (hupper n hn)
  have habpos : ∀ᶠ n in atTop, 0 < A n+B n := by
    filter_upwards [hapos, hbnonneg] with n ha hb
    linarith
  have hlow : ∀ᶠ n in atTop,
      A n/(n : ℝ) ≤ (P n).real (E n) := by
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
    simpa only [hrealPos n hn] using (hcount n hn).1
  have hupp : ∀ᶠ n in atTop,
      (P n).real (E n) ≤ 2*(A n+B n) := by
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
    have hh := (hcount n hn).2
    rw [hrealPos n hn, hrealNeg n hn] at hh
    linarith [hnonreal n hn]
  exact first_moment_tail_transfer A (fun n => A n+B n)
    (fun n => (P n).real (E n)) L
    hapos habpos hArate hABrate hlow hupp

#print axioms three_count_event_rate_from_analytic
end SpectralRadiusUpperTail
