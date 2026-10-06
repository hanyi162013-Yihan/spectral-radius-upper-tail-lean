import SpectralRadiusUpperTail.IidWordCount

namespace SpectralRadiusUpperTail
variable {σ τ υ : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ] [Fintype υ]

lemma entryMultiplicity_pos_iff (e : τ → σ) (i : σ) :
    0 < entryMultiplicity e i ↔ ∃ j, e j = i := by
  rw [entryMultiplicity, Finset.card_pos]
  constructor
  · rintro ⟨j,hj⟩
    exact ⟨j,(Finset.mem_filter.mp hj).2⟩
  · rintro ⟨j,hj⟩
    exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩

lemma entryPairSupport_eq_images (e : τ → σ) (f : υ → σ) :
    entryPairSupport e f = Finset.univ.image e ∪ Finset.univ.image f := by
  ext i
  simp [entryPairSupport, entryMultiplicity_pos_iff]

lemma entryMultiplicity_of_injective (e : τ → σ) (he : Function.Injective e) (j : τ) :
    entryMultiplicity e (e j) = 1 := by
  classical
  have hf : Finset.univ.filter (fun x => e x = e j) = {j} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton, he.eq_iff]
  simp only [entryMultiplicity, hf, Finset.card_singleton]

#print axioms entryMultiplicity_pos_iff
#print axioms entryPairSupport_eq_images
#print axioms entryMultiplicity_of_injective
end SpectralRadiusUpperTail
