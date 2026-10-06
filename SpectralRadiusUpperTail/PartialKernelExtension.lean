import SpectralRadiusUpperTail.FiniteFiberGluing

namespace SpectralRadiusUpperTail
variable {A B : Type*} [Fintype A] [DecidableEq A]

/-- Knowing the equality pattern on S, at most one additional pair per
missing position recovers the equality pattern on all positions. Representatives
are chosen inside S whenever their fiber meets S. -/
lemma exists_partial_kernel_extension (f : A → B) (S : Finset A) :
    ∃ E : Finset (A × A), E.card ≤ Fintype.card A - S.card ∧
      ∀ x y, Relation.EqvGen
        (fun a b => (a ∈ S ∧ b ∈ S ∧ f a = f b) ∨ (a,b) ∈ E) x y ↔ f x = f y := by
  classical
  have hex (b : Set.range f) : ∃ a, f a = b.val ∧
      ((∃ x ∈ S, f x = b.val) → a ∈ S) := by
    by_cases hb : ∃ x ∈ S, f x = b.val
    · obtain ⟨a,ha,hfa⟩ := hb
      exact ⟨a,hfa,fun _ => ha⟩
    · obtain ⟨a,hfa⟩ := b.property
      exact ⟨a,hfa,fun h => (hb h).elim⟩
  let g : Set.range f → A := fun b => Classical.choose (hex b)
  have hg (b : Set.range f) : f (g b) = b.val := (Classical.choose_spec (hex b)).1
  have hS (b : Set.range f) : (∃ x ∈ S, f x = b.val) → g b ∈ S :=
    (Classical.choose_spec (hex b)).2
  let q : A → Set.range f := fun a => ⟨f a, a, rfl⟩
  let E : Finset (A × A) := Sᶜ.image (fun a => (a,g (q a)))
  have hE : ∀ a b, (a,b) ∈ E → f a = f b := by
    intro a b hab
    obtain ⟨z,_,hz⟩ := Finset.mem_image.mp hab
    have ha : z = a := congrArg Prod.fst hz
    have hb : g (q z) = b := congrArg Prod.snd hz
    subst a
    rw [← hb, hg]
  refine ⟨E,?_,?_⟩
  · exact (Finset.card_image_le).trans_eq (Finset.card_compl S)
  · intro x y
    constructor
    · intro h
      induction h with
      | rel a b h => exact h.elim (fun h => h.2.2) (hE a b)
      | refl => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    · intro hxy
      have join (a : A) : Relation.EqvGen
          (fun a b => (a ∈ S ∧ b ∈ S ∧ f a = f b) ∨ (a,b) ∈ E) a (g (q a)) := by
        apply Relation.EqvGen.rel
        by_cases ha : a ∈ S
        · exact Or.inl ⟨ha,hS (q a) ⟨a,ha,rfl⟩,(hg (q a)).symm⟩
        · exact Or.inr (Finset.mem_image.mpr ⟨a,Finset.mem_compl.mpr ha,rfl⟩)
      have hq : q x = q y := Subtype.ext hxy
      have hx := join x
      rw [hq] at hx
      exact Relation.EqvGen.trans _ _ _ hx (Relation.EqvGen.symm _ _ (join y))

#print axioms exists_partial_kernel_extension
end SpectralRadiusUpperTail
