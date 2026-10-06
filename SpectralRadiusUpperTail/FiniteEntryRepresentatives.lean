import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- Choose exactly one representative in a finite domain for each prescribed image. -/
lemma finset_image_representatives {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (f : α → β) (h : B ⊆ A.image f) :
    ∃ T : Finset α, T ⊆ A ∧ T.image f = B ∧ Set.InjOn f T ∧ T.card = B.card := by
  classical
  have hex : ∀ y : B, ∃ x : α, x ∈ A ∧ f x = y.val := by
    intro y
    exact Finset.mem_image.mp (h y.property)
  choose g hg using hex
  have hgi : Function.Injective g := by
    intro y z hyz
    apply Subtype.ext
    exact (hg y).2.symm.trans ((congrArg f hyz).trans (hg z).2)
  let T := B.attach.image g
  have hsub : T ⊆ A := by
    intro x hx
    obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hx
    exact (hg y).1
  have him : T.image f = B := by
    ext y
    constructor
    · intro hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hx
      rw [(hg z).2]
      exact z.property
    · intro hy
      exact Finset.mem_image.mpr ⟨g ⟨y,hy⟩,
        Finset.mem_image.mpr ⟨⟨y,hy⟩,Finset.mem_attach _ _,rfl⟩,(hg ⟨y,hy⟩).2⟩
  have hinj : Set.InjOn f T := by
    intro x hx y hy hxy
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hy
    have hab : a = b := Subtype.ext ((hg a).2.symm.trans (hxy.trans (hg b).2))
    exact congrArg g hab
  refine ⟨T,hsub,him,hinj,?_⟩
  rw [← him, Finset.card_image_of_injOn hinj]

#print axioms finset_image_representatives
end SpectralRadiusUpperTail
