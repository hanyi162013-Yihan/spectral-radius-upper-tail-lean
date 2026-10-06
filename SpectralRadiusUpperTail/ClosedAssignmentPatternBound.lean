import SpectralRadiusUpperTail.OrientedAssignmentMoment
import SpectralRadiusUpperTail.EqualityPatternSum

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {ι 𝕂 : Type*} [Fintype ι] [RCLike 𝕂]
  [MeasurableSpace 𝕂] [BorelSpace 𝕂] {r : ℕ}

noncomputable def closedAssignmentWeight (μ : Measure 𝕂) (s : Fin (2*r) → Bool)
    (v : Fin (2*r+1) → ι) : ℝ := by
  classical
  exact if v (Fin.last (2*r)) = v 0 then ‖orientedAssignmentMoment μ s v‖ else 0

lemma closedAssignmentWeight_nonneg (μ : Measure 𝕂) (s : Fin (2*r) → Bool)
    (v : Fin (2*r+1) → ι) : 0 ≤ closedAssignmentWeight μ s v := by
  classical
  unfold closedAssignmentWeight
  split <;> positivity

lemma closedAssignmentWeight_relabel (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (s : Fin (2*r) → Bool) (R : Setoid (Fin (2*r+1))) [DecidableRel R.r]
    (f : Quotient R → ι) (hf : Function.Injective f) :
    closedAssignmentWeight μ s (fun a => f (Quotient.mk R a)) =
      if R.r (Fin.last (2*r)) 0 then ‖orientedPatternMoment μ s R‖ else 0 := by
  classical
  unfold closedAssignmentWeight
  rw [orientedPatternMoment_relabel μ s R f hf]
  simp only [hf.eq_iff, Quotient.eq]

attribute [local instance] Classical.propDecidable

lemma closedAssignmentPatternContribution_le (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (s : Fin (2*r) → Bool) (R : Setoid (Fin (2*r+1))) :
    equalityPatternContribution R (closedAssignmentWeight (ι := ι) μ s) ≤
      (Fintype.card ι : ℝ)^(Nat.card (Quotient R)) *
        (if R.r (Fin.last (2*r)) 0 then ‖orientedPatternMoment μ s R‖ else 0) := by
  classical
  unfold equalityPatternContribution
  simp_rw [closedAssignmentWeight_relabel μ s R _ (Subtype.property _)]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right
  · have hcard := Fintype.card_subtype_le (fun f : Quotient R → ι => Function.Injective f)
    rw [Fintype.card_fun] at hcard
    simpa only [Nat.card_eq_fintype_card, Nat.cast_pow] using (Nat.cast_le (α := ℝ)).mpr hcard
  · split <;> positivity

#print axioms closedAssignmentWeight
#print axioms closedAssignmentWeight_nonneg
#print axioms closedAssignmentWeight_relabel
#print axioms closedAssignmentPatternContribution_le
end SpectralRadiusUpperTail
