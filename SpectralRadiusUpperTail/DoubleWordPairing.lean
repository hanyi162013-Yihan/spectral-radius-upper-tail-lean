import SpectralRadiusUpperTail.MultiplicityTwoPositions

namespace SpectralRadiusUpperTail
variable {σ τ : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ]

lemma doubleWord_unique_partner (e : τ → σ)
    (h : ∀ i, entryMultiplicity e (e i) = 2) (i : τ) :
    ∃! j, j ≠ i ∧ e j = e i := by
  classical
  obtain ⟨a,b,hab,hpos⟩ := entryMultiplicity_two_positions e (e i) (h i)
  have hi := (hpos i).mp rfl
  rcases hi with hi | hi
  · subst i
    refine ⟨b,⟨Ne.symm hab,(hpos b).mpr (Or.inr rfl)⟩,?_⟩
    intro j hj
    rcases (hpos j).mp hj.2 with hj' | hj'
    · exact False.elim (hj.1 hj')
    · exact hj'
  · subst i
    refine ⟨a,⟨hab,(hpos a).mpr (Or.inl rfl)⟩,?_⟩
    intro j hj
    rcases (hpos j).mp hj.2 with hj' | hj'
    · exact hj'
    · exact False.elim (hj.1 hj')

noncomputable def doubleWordPartner (e : τ → σ)
    (h : ∀ i, entryMultiplicity e (e i) = 2) (i : τ) : τ :=
  Classical.choose (doubleWord_unique_partner e h i)

lemma doubleWordPartner_spec (e : τ → σ)
    (h : ∀ i, entryMultiplicity e (e i) = 2) (i : τ) :
    doubleWordPartner e h i ≠ i ∧ e (doubleWordPartner e h i) = e i :=
  (Classical.choose_spec (doubleWord_unique_partner e h i)).1

lemma doubleWordPartner_involutive (e : τ → σ)
    (h : ∀ i, entryMultiplicity e (e i) = 2) :
    Function.Involutive (doubleWordPartner e h) := by
  intro i
  have hs := doubleWordPartner_spec e h i
  have hi : i ≠ doubleWordPartner e h i ∧ e i = e (doubleWordPartner e h i) :=
    ⟨Ne.symm hs.1,hs.2.symm⟩
  exact ((Classical.choose_spec (doubleWord_unique_partner e h (doubleWordPartner e h i))).2 i hi).symm

#print axioms doubleWord_unique_partner
#print axioms doubleWordPartner
#print axioms doubleWordPartner_spec
#print axioms doubleWordPartner_involutive
end SpectralRadiusUpperTail
