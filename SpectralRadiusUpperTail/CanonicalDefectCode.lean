import SpectralRadiusUpperTail.ArrangementCodeFinite
import SpectralRadiusUpperTail.CanonicalMatchingInjective

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators

/-- Bounds on all non-matching data in a full defect code. The number of
segments is recorded separately by the finite outer index. -/
abbrev BoundedDefectCode {L : ℕ} (s : Fin L → Bool) (g : ℕ) :=
  Σ S : Fin (8*g+2), {C : ArrangementKernelCode s S.val //
    C.arrangement.deleted.card ≤ 8*g ∧
    Fintype.card C.kernel.family.VertexSlot ≤ 2*L ∧
    C.kernel.gluing.card ≤ 8*g ∧ C.kernel.restoration.card ≤ 8*g+1}

variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂] {r : ℕ}

/-- Every genuine nonzero centered iid canonical pattern admits the actual
bounded code. This does not assume an abstract encoding/count hypothesis. -/
lemma orientedPattern_exists_bounded_code (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (s : Fin (2*r) → Bool)
    (R : Setoid (Fin (2*r+1))) [DecidableRel R.r]
    (hn : orientedPatternMoment μ s R ≠ 0) :
    ∃ C : BoundedDefectCode s (r+1-Fintype.card (Quotient R)), C.2.val.decode = R := by
  have hsur : Function.Surjective (Quotient.mk R) := by
    intro x
    exact Quotient.inductionOn x (fun a => ⟨a,rfl⟩)
  obtain ⟨c⟩ := orientedWalk_defect_route_certificate μ hm s (Quotient.mk R) hsur hn
  obtain ⟨C,hdec,hD,hslot,hE,hF⟩ := c.exists_arrangement_kernel_code
  refine ⟨⟨⟨c.segments.length,by have h := c.segment_budget; omega⟩,C,hD,?_,hE,hF⟩,?_⟩
  · simpa only [show 2*(2*r) = 4*r by omega] using hslot
  · exact hdec.trans (by apply Setoid.ext; intro a b; exact Quotient.eq)

noncomputable abbrev NonzeroDefectPattern (μ : Measure 𝕂) (s : Fin (2*r) → Bool) (g : ℕ) : Type := by
  classical
  exact {R : Setoid (Fin (2*r+1)) // orientedPatternMoment μ s R ≠ 0 ∧
    r+1-Nat.card (Quotient R) = g}

/-- Equal complete codes force equality of canonical setoids. The bound on
how many codes exist is a separate, quantitative counting step. -/
lemma nonzeroDefectPattern_count_le_code (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (s : Fin (2*r) → Bool) (g : ℕ) :
    Nat.card (NonzeroDefectPattern μ s g) ≤ Nat.card (BoundedDefectCode s g) := by
  classical
  have hex (R : NonzeroDefectPattern μ s g) :
      ∃ C : BoundedDefectCode s g, C.2.val.decode = R.val := by
    rcases R with ⟨R,hn,hg⟩
    have h := orientedPattern_exists_bounded_code μ hm s R hn
    have hc : r+1-Fintype.card (Quotient R) = g := by
      simpa only [Nat.card_eq_fintype_card] using hg
    rw [hc] at h
    exact h
  let encode : NonzeroDefectPattern μ s g → BoundedDefectCode s g :=
    fun R => Classical.choose (hex R)
  have hinj : Function.Injective encode := by
    intro R S h
    apply Subtype.ext
    exact (Classical.choose_spec (hex R)).symm.trans
      ((congrArg (fun C : BoundedDefectCode s g => C.2.val.decode) h).trans (Classical.choose_spec (hex S)))
  exact Nat.card_le_card_of_injective encode hinj

#print axioms BoundedDefectCode
#print axioms orientedPattern_exists_bounded_code
#print axioms NonzeroDefectPattern
#print axioms nonzeroDefectPattern_count_le_code
end SpectralRadiusUpperTail
