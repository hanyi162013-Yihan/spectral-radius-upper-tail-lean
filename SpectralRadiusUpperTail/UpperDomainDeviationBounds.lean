import SpectralRadiusUpperTail.OpenUpperTailLower
import SpectralRadiusUpperTail.ClosedUpperTailUpper
import SpectralRadiusUpperTail.RateSublevels

namespace SpectralRadiusUpperTail
open MeasureTheory Filter Set

/-- Open/closed set estimates in the strictly upper-tail region (1,∞).
This does not assert the missing behavior at or below one. Empty sets are
excluded from the real-valued infimum formulation. -/
def UpperDomainDeviationBounds
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) (X : (n : ℕ) → Ω n → ℝ) (β : ℝ) : Prop :=
  (∀ U : Set ℝ, IsOpen U → U.Nonempty → (∀ r ∈ U, 1 < r) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      Real.exp ((n : ℝ)*(-sInf (rate β '' U)-ε)) ≤ (μ n).real {ω | X n ω ∈ U}) ∧
  (∀ F : Set ℝ, IsClosed F → F.Nonempty → (∀ r ∈ F, 1 < r) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (μ n).real {ω | X n ω ∈ F} ≤ Real.exp ((n : ℝ)*(-sInf (rate β '' F)+ε)))

lemma upper_domain_deviation_bounds_of_tails
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (X : (n : ℕ) → Ω n → ℝ) (β : ℝ) (hβ : 0 < β)
    (htails : ∀ r : ℝ, 1 < r → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      Real.exp ((n : ℝ)*(-rate β r-ε)) ≤ (μ n).real {x | r < X n x} ∧
      (μ n).real {x | r ≤ X n x} ≤ Real.exp ((n : ℝ)*(-rate β r+ε))) :
    UpperDomainDeviationBounds Ω μ X β := by
  constructor
  · exact open_set_exponential_lower_rate_infimum Ω μ X β hβ htails
  · apply closed_set_exponential_upper_above_one Ω μ X β hβ
    intro r hr ε hε
    exact (htails r hr ε hε).mono (fun _ h => h.2)

#print axioms upper_domain_deviation_bounds_of_tails
end SpectralRadiusUpperTail
