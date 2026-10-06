import SpectralRadiusUpperTail.OrientedSupportCardinality

namespace SpectralRadiusUpperTail
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Directed entries with their endpoints restricted to a specified vertex set. -/
noncomputable def restrictedEntries (E : Finset (V × V)) (S : Set V) : Finset (S × S) := by
  classical
  exact Finset.univ.filter (fun e => (e.1.val,e.2.val) ∈ E)

lemma restrictedEntries_graph (E : Finset (V × V)) (S : Set V) :
    walkSupportGraph (restrictedEntries E S) = (walkSupportGraph E).induce S := by
  classical
  ext a b
  change (a ≠ b ∧ ((a,b) ∈ restrictedEntries E S ∨ (b,a) ∈ restrictedEntries E S)) ↔
    (a.val ≠ b.val ∧ ((a.val,b.val) ∈ E ∨ (b.val,a.val) ∈ E))
  simp only [restrictedEntries, Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_congr (not_congr Subtype.val_injective.eq_iff.symm) Iff.rfl

lemma restrictedEntries_image (E : Finset (V × V)) (S : Set V)
    (hS : ∀ e ∈ E, e.1 ∈ S ∧ e.2 ∈ S) :
    (restrictedEntries E S).image (Prod.map Subtype.val Subtype.val) = E := by
  classical
  ext e
  constructor
  · intro h
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp h
    exact (Finset.mem_filter.mp hab).2
  · intro he
    exact Finset.mem_image.mpr ⟨(⟨e.1,(hS e he).1⟩,⟨e.2,(hS e he).2⟩),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩,rfl⟩

lemma restrictedEntries_card (E : Finset (V × V)) (S : Set V)
    (hS : ∀ e ∈ E, e.1 ∈ S ∧ e.2 ∈ S) : (restrictedEntries E S).card = E.card := by
  classical
  have hi : Function.Injective (Prod.map (Subtype.val : S → V) (Subtype.val : S → V)) := by
    intro x y h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  exact (Finset.card_image_of_injective (restrictedEntries E S) hi).symm.trans
    (congrArg Finset.card (restrictedEntries_image E S hS))

lemma restrictedEntries_isAcyclic (E : Finset (V × V)) (S : Set V)
    (ha : (walkSupportGraph E).IsAcyclic) :
    (walkSupportGraph (restrictedEntries E S)).IsAcyclic := by
  rw [restrictedEntries_graph]
  exact ha.induce S

#print axioms restrictedEntries
#print axioms restrictedEntries_graph
#print axioms restrictedEntries_image
#print axioms restrictedEntries_card
#print axioms restrictedEntries_isAcyclic
end SpectralRadiusUpperTail
