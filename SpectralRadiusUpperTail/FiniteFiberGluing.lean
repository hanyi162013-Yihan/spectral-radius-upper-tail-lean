import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Relation

namespace SpectralRadiusUpperTail

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]

/-- One pair joins each nonrepresentative to its chosen fiber representative. -/
noncomputable def fiberGluingPairs (f : α → β) (g : β → α) : Finset (α × α) :=
  ((Finset.univ : Finset α) \ Finset.univ.image g).image (fun x => (x, g (f x)))

lemma fiberGluingPairs_card (f : α → β) (g : β → α)
    (hg : Function.RightInverse g f) :
    (fiberGluingPairs f g).card = Fintype.card α - Fintype.card β := by
  classical
  unfold fiberGluingPairs
  rw [Finset.card_image_of_injective _ (by
    intro x y h
    exact congrArg Prod.fst h)]
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  rw [Finset.card_image_of_injective _ hg.injective]
  simp

lemma fiberGluingPairs_same_fiber (f : α → β) (g : β → α)
    (hg : Function.RightInverse g f) {x y : α}
    (h : (x,y) ∈ fiberGluingPairs f g) : f x = f y := by
  classical
  obtain ⟨z, _, hz⟩ := Finset.mem_image.mp h
  have hx : z = x := congrArg Prod.fst hz
  have hy : g (f z) = y := congrArg Prod.snd hz
  subst x
  rw [← hy, hg (f z)]

/-- Closing the representative pairs under equivalence recovers precisely
all equal-image identifications, including singleton and empty fibers. -/
lemma fiberGluingPairs_eqvGen_iff (f : α → β) (g : β → α)
    (hg : Function.RightInverse g f) (x y : α) :
    Relation.EqvGen (fun a b => (a,b) ∈ fiberGluingPairs f g) x y ↔ f x = f y := by
  classical
  constructor
  · intro h
    induction h with
    | rel a b h => exact fiberGluingPairs_same_fiber f g hg h
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · intro hxy
    have join : ∀ a, Relation.EqvGen
        (fun a b => (a,b) ∈ fiberGluingPairs f g) a (g (f a)) := by
      intro a
      by_cases ha : a ∈ (Finset.univ : Finset β).image g
      · obtain ⟨b, _, hb⟩ := Finset.mem_image.mp ha
        have he : g (f a) = a := by rw [← hb, hg b]
        rw [he]
        exact Relation.EqvGen.refl _
      · apply Relation.EqvGen.rel
        apply Finset.mem_image.mpr
        exact ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩, rfl⟩
    have hx := join x
    have hy := join y
    rw [hxy] at hx
    exact Relation.EqvGen.trans _ _ _ hx (Relation.EqvGen.symm _ _ hy)

/-- A finite surjection is encoded by exactly the cardinality deficit many
pairs; this is an encoding of its kernel, not of the target labels. -/
lemma exists_finite_fiber_gluing (f : α → β) (hf : Function.Surjective f) :
    ∃ E : Finset (α × α),
      E.card = Fintype.card α - Fintype.card β ∧
      ∀ x y, Relation.EqvGen (fun a b => (a,b) ∈ E) x y ↔ f x = f y := by
  classical
  let g : β → α := fun b => Classical.choose (hf b)
  have hg : Function.RightInverse g f := fun b => Classical.choose_spec (hf b)
  exact ⟨fiberGluingPairs f g, fiberGluingPairs_card f g hg,
    fiberGluingPairs_eqvGen_iff f g hg⟩

#print axioms fiberGluingPairs
#print axioms fiberGluingPairs_card
#print axioms fiberGluingPairs_same_fiber
#print axioms fiberGluingPairs_eqvGen_iff
#print axioms exists_finite_fiber_gluing
end SpectralRadiusUpperTail
