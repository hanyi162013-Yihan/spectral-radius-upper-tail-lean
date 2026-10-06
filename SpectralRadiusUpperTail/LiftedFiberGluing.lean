import SpectralRadiusUpperTail.FiniteFiberGluing

namespace SpectralRadiusUpperTail
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C] [DecidableEq A]

/-- Lift a kernel generating set from local quotient vertices to original
positions. The existing local equalities plus exactly card(B)-card(C) pairs
recover all global equalities; the pairs use only original positions. -/
lemma exists_lifted_fiber_gluing (p : A → B) (hp : Function.Surjective p)
    (f : B → C) (hf : Function.Surjective f) :
    ∃ E : Finset (A × A), E.card = Fintype.card B - Fintype.card C ∧
      ∀ x y, Relation.EqvGen (fun a b => p a = p b ∨ (a,b) ∈ E) x y ↔
        f (p x) = f (p y) := by
  classical
  let g : B → A := fun b => Classical.choose (hp b)
  have hg : Function.RightInverse g p := fun b => Classical.choose_spec (hp b)
  obtain ⟨D,hD,hrec⟩ := exists_finite_fiber_gluing f hf
  let E := D.image (Prod.map g g)
  have hi : Function.Injective (Prod.map g g) := by
    intro x y h
    exact Prod.ext (hg.injective (congrArg Prod.fst h)) (hg.injective (congrArg Prod.snd h))
  have hc : E.card = Fintype.card B - Fintype.card C :=
    (Finset.card_image_of_injective D hi).trans hD
  have hsame {a b : A} (h : (a,b) ∈ E) : f (p a) = f (p b) := by
    obtain ⟨⟨u,v⟩,huv,h⟩ := Finset.mem_image.mp h
    have ha : g u = a := congrArg Prod.fst h
    have hb : g v = b := congrArg Prod.snd h
    rw [← ha,← hb,hg u,hg v]
    exact (hrec u v).mp (Relation.EqvGen.rel _ _ huv)
  have lift {u v : B} (h : Relation.EqvGen (fun a b => (a,b) ∈ D) u v) :
      Relation.EqvGen (fun a b => p a = p b ∨ (a,b) ∈ E) (g u) (g v) := by
    induction h with
    | rel u v h => exact Relation.EqvGen.rel _ _ (Or.inr (Finset.mem_image.mpr ⟨(u,v),h,rfl⟩))
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  refine ⟨E,hc,?_⟩
  intro x y
  constructor
  · intro h
    induction h with
    | rel a b h => exact h.elim (congrArg f) hsame
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · intro h
    have hx : Relation.EqvGen (fun a b => p a = p b ∨ (a,b) ∈ E) x (g (p x)) :=
      Relation.EqvGen.rel _ _ (Or.inl (hg (p x)).symm)
    have hy : Relation.EqvGen (fun a b => p a = p b ∨ (a,b) ∈ E) (g (p y)) y :=
      Relation.EqvGen.rel _ _ (Or.inl (hg (p y)))
    exact Relation.EqvGen.trans _ _ _ hx
      (Relation.EqvGen.trans _ _ _ (lift ((hrec _ _).mpr h)) hy)

#print axioms exists_lifted_fiber_gluing
end SpectralRadiusUpperTail
