import SpectralRadiusUpperTail.ClosedPatternWeightedSum

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂] {r : ℕ}
attribute [local instance] Classical.propDecidable

lemma closedPatternWeight_fiber_count (μ : Measure 𝕂) (s : Fin (2*r) → Bool)
    (n g : ℕ) :
    Nat.card {R : Setoid (Fin (2*r+1)) // closedPatternWeight μ s n R ≠ 0 ∧
      r+1-Nat.card (Quotient R) = g} ≤ Nat.card (ClosedDefectPattern μ s g) := by
  classical
  let f : {R : Setoid (Fin (2*r+1)) // closedPatternWeight μ s n R ≠ 0 ∧
      r+1-Nat.card (Quotient R) = g} → ClosedDefectPattern μ s g := fun R =>
    ⟨R.val,(closedPatternWeight_nonzero μ s n R.val R.property.1).1,
      (closedPatternWeight_nonzero μ s n R.val R.property.1).2,R.property.2⟩
  apply Nat.card_le_card_of_injective f
  intro R S h
  apply Subtype.ext
  exact congrArg (fun T => T.val) h

lemma closedPatternWeight_sum_le (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (hv : (∫ z : 𝕂, ‖z‖^2 ∂μ) = 1)
    (s : Fin (2*r) → Bool) (n : ℕ) :
    ∑ R : Setoid (Fin (2*r+1)), closedPatternWeight μ s n R ≤
      ∑ g : Fin (r+1), (Nat.card (ClosedDefectPattern μ s g.val) : ℝ) *
        ((n : ℝ)^(r+1-g.val) * (signedWordMomentBase μ c (2*r))^(6*g.val)) := by
  classical
  have ha := signedWordMomentBase_one_le μ c hc (2*r)
  apply (finite_sum_le_defect_counts (closedPatternWeight μ s n)
    (fun R => r+1-Nat.card (Quotient R)) r
    (fun g => (n : ℝ)^(r+1-g) * (signedWordMomentBase μ c (2*r))^(6*g))
    (closedPatternWeight_nonneg μ s n)
    (fun R _ => closedPatternWeight_defect_range μ s n R)
    (closedPatternWeight_defect_le μ c hc hexp hm hv s n)).trans
  apply Finset.sum_le_sum
  intro g _
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast closedPatternWeight_fiber_count μ s n g.val
  · positivity

#print axioms closedPatternWeight_fiber_count
#print axioms closedPatternWeight_sum_le
end SpectralRadiusUpperTail
