import SpectralRadiusUpperTail.ClosedDefectPatternCount
import SpectralRadiusUpperTail.FiniteDefectSum

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂] {r : ℕ}
attribute [local instance] Classical.propDecidable

noncomputable def closedPatternWeight (μ : Measure 𝕂) (s : Fin (2*r) → Bool)
    (n : ℕ) (R : Setoid (Fin (2*r+1))) : ℝ :=
  if R.r (Fin.last (2*r)) 0 then
    (n : ℝ)^(Nat.card (Quotient R)) * ‖orientedPatternMoment μ s R‖ else 0

lemma closedPatternWeight_nonneg (μ : Measure 𝕂) (s : Fin (2*r) → Bool)
    (n : ℕ) (R : Setoid (Fin (2*r+1))) : 0 ≤ closedPatternWeight μ s n R := by
  unfold closedPatternWeight
  split <;> positivity

lemma closedPatternWeight_nonzero (μ : Measure 𝕂) (s : Fin (2*r) → Bool)
    (n : ℕ) (R : Setoid (Fin (2*r+1))) (h : closedPatternWeight μ s n R ≠ 0) :
    orientedPatternMoment μ s R ≠ 0 ∧ R.r (Fin.last (2*r)) 0 := by
  unfold closedPatternWeight at h
  split at h
  · rename_i hc
    exact ⟨fun hz => h (by simp [hz]),hc⟩
  · exact (h rfl).elim

lemma closedPatternWeight_defect_le (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (hv : (∫ z : 𝕂, ‖z‖^2 ∂μ) = 1)
    (s : Fin (2*r) → Bool) (n : ℕ) (R : Setoid (Fin (2*r+1)))
    (h : closedPatternWeight μ s n R ≠ 0) :
    closedPatternWeight μ s n R ≤
      (n : ℝ)^(r+1-(r+1-Nat.card (Quotient R))) *
        (signedWordMomentBase μ c (2*r))^(6*(r+1-Nat.card (Quotient R))) := by
  have hh := closedPatternWeight_nonzero μ s n R h
  have hcard := orientedPatternMoment_nonzero_vertices μ hm s R hh.1
  have he : r+1-(r+1-Nat.card (Quotient R)) = Nat.card (Quotient R) := by
    simp only [Nat.card_eq_fintype_card] at *
    omega
  rw [he,closedPatternWeight,if_pos hh.2]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [Nat.card_eq_fintype_card] using
    orientedPatternMoment_vertex_defect_le μ c hc hexp hm hv s R

lemma closedPatternWeight_defect_range (μ : Measure 𝕂) (s : Fin (2*r) → Bool)
    (n : ℕ) (R : Setoid (Fin (2*r+1))) : r+1-Nat.card (Quotient R) ≤ r := by
  have hp : 0 < Nat.card (Quotient R) := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.mpr ⟨Quotient.mk R 0⟩
  omega

#print axioms closedPatternWeight
#print axioms closedPatternWeight_nonneg
#print axioms closedPatternWeight_nonzero
#print axioms closedPatternWeight_defect_le
#print axioms closedPatternWeight_defect_range
end SpectralRadiusUpperTail
