import SpectralRadiusUpperTail.OrientedWalkTreeCase
import SpectralRadiusUpperTail.IidDoubleWordValue

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂] {r : ℕ}

lemma orientedPattern_extremal_degrees (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (s : Fin (2*r) → Bool)
    (R : Setoid (Fin (2*r+1))) [DecidableRel R.r]
    (hn : orientedPatternMoment μ s R ≠ 0) (hc : Fintype.card (Quotient R) = r+1) :
    ∀ e, entryMultiplicity (orientedWalkEdge s (Quotient.mk R)) e = 0 ∨
      entryMultiplicity (orientedWalkEdge s (Quotient.mk R)) e = 2 := by
  have hcover : Function.Surjective (Quotient.mk R) := by
    intro x
    exact Quotient.inductionOn x (fun a => ⟨a,rfl⟩)
  have ht := orientedWalk_extremal_tree μ hm s (Quotient.mk R) hcover hn hc
  intro e
  by_cases he : 0 < entryMultiplicity (orientedWalkEdge s (Quotient.mk R)) e
  · right
    apply ht.2.2.2 e
    obtain ⟨a,ha⟩ := (entryMultiplicity_pos_iff _ _).mp he
    exact Finset.mem_image.mpr ⟨a,Finset.mem_univ a,ha⟩
  · left
    omega

lemma orientedPattern_proper_tree_value (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (hp : (∫ z : 𝕂, z^2 ∂μ) = 0)
    (hv : (∫ z : 𝕂, ‖z‖^2 ∂μ) = 1) (s : Fin (2*r) → Bool)
    (R : Setoid (Fin (2*r+1))) [DecidableRel R.r]
    (hn : orientedPatternMoment μ s R ≠ 0) (hc : Fintype.card (Quotient R) = r+1) :
    orientedPatternMoment μ s R = 1 :=
  iidProperDoubleWord_expectation_one μ hp hv (orientedWalkEdge s (Quotient.mk R)) s
    (orientedPattern_extremal_degrees μ hm s R hn hc) hn

lemma orientedPattern_real_tree_value (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : (∫ z : ℝ, z ∂μ) = 0) (hv : (∫ z : ℝ, ‖z‖^2 ∂μ) = 1)
    (s : Fin (2*r) → Bool) (R : Setoid (Fin (2*r+1))) [DecidableRel R.r]
    (hn : orientedPatternMoment μ s R ≠ 0) (hc : Fintype.card (Quotient R) = r+1) :
    orientedPatternMoment μ s R = 1 :=
  iidRealDoubleWord_expectation_one μ hv (orientedWalkEdge s (Quotient.mk R)) s
    (orientedPattern_extremal_degrees μ hm s R hn hc)

#print axioms orientedPattern_extremal_degrees
#print axioms orientedPattern_proper_tree_value
#print axioms orientedPattern_real_tree_value
end SpectralRadiusUpperTail
